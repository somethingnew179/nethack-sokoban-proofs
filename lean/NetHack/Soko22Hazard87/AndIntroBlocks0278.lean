import NetHack.Soko22Hazard87.AndIntroBlocks0277
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro69500 (p : Pattern) (ha : d273893 p = 1) (hb : d275870 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d273888 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d273763 q = 1) (hb : d275564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d273763, d275564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69149 q ha hb
    | true =>
      simp only [d273763, d275564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d273889 q = 1) (hb : d275866 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d273889, d275866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d273889, d275866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d273764 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d273890 q = 1) (hb : d275867 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d273890, d275867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d273890, d275867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d273891 q = 1) (hb : d275868 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d273891, d275868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d273891, d275868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d273892 q = 1) (hb : d275869 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d273892, d275869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d273892, d275869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d273893 q = 1) (hb : d275870 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d273893, d275870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d273893, d275870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69501 (p : Pattern) (ha : d273899 p = 1) (hb : d277233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d273794 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d273856 q = 1) (hb : d275593 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d273856, d275593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69497 q ha hb
    | true =>
      simp only [d273856, d275593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69498 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d273858 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d273859 q = 1) (hb : d275594 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d273859, d275594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d273859, d275594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d273860 q = 1) (hb : d277223 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d273860, d277223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d273860, d277223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d273861 q = 1) (hb : d277224 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d273861, d277224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d273861, d277224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d273865 q = 1) (hb : d275821 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d273865, d275821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d273865, d275821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69499 q ha hb
  have h8 (q : Pattern) (ha : d273866 q = 1) (hb : d277225 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d273866, d277225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d273866, d277225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d273867 q = 1) (hb : d277226 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d273867, d277226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d273867, d277226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d273868 q = 1) (hb : d277227 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d273868, d277227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d273868, d277227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d273869 q = 1) (hb : d277228 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d273869, d277228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d273869, d277228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d273894 q = 1) (hb : d275871 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d273894, d275871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d273894, d275871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69500 q ha hb
  have h13 (q : Pattern) (ha : d273895 q = 1) (hb : d277229 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d273895, d277229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d273895, d277229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d273896 q = 1) (hb : d277230 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d273896, d277230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d273896, d277230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d273897 q = 1) (hb : d277231 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d273897, d277231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d273897, d277231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d273898 q = 1) (hb : d277232 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d273898, d277232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d273898, d277232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d273899 q = 1) (hb : d277233 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d273899, d277233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d273899, d277233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro69502 (p : Pattern) (ha : d273905 p = 1) (hb : d277239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d273779 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d273900 q = 1) (hb : d277234 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d273900, d277234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d273900, d277234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69501 q ha hb
  have h3 (q : Pattern) (ha : d273901 q = 1) (hb : d277235 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d273901, d277235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d273901, d277235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d273902 q = 1) (hb : d277236 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d273902, d277236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d273902, d277236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d273903 q = 1) (hb : d277237 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d273903, d277237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d273903, d277237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d273904 q = 1) (hb : d277238 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d273904, d277238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d273904, d277238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d273905 q = 1) (hb : d277239 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d273905, d277239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d273905, d277239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro69503 (p : Pattern) (ha : d273978 p = 1) (hb : d275711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d273926 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d273932 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d273967 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d273834 q = 1) (hb : d275635 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d273834, d275635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69160 q ha hb
    | true =>
      simp only [d273834, d275635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69142 q ha hb
  have h5 (q : Pattern) (ha : d273968 q = 1) (hb : d275707 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d273968, d275707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d273968, d275707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d273974 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d273975 q = 1) (hb : d275708 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d273975, d275708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d273975, d275708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d273976 q = 1) (hb : d275709 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d273976, d275709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d273976, d275709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d273977 q = 1) (hb : d275710 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d273977, d275710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d273977, d275710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d273978 q = 1) (hb : d275711 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d273978, d275711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d273978, d275711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro69504 (p : Pattern) (ha : d273997 p = 1) (hb : d275718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d273926 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d273932 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d273967 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d273834 q = 1) (hb : d275635 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d273834, d275635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69160 q ha hb
    | true =>
      simp only [d273834, d275635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69142 q ha hb
  have h4 (q : Pattern) (ha : d273968 q = 1) (hb : d275707 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d273968, d275707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d273968, d275707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d273974 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d273975 q = 1) (hb : d275708 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d273975, d275708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d273975, d275708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d273976 q = 1) (hb : d275709 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d273976, d275709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d273976, d275709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d273977 q = 1) (hb : d275710 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d273977, d275710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d273977, d275710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d273983 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d273987 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d273989 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d273850 q = 1) (hb : d275651 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d273850, d275651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69164 q ha hb
    | true =>
      simp only [d273850, d275651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69144 q ha hb
  have h13 (q : Pattern) (ha : d273990 q = 1) (hb : d275714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d273990, d275714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d273990, d275714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d273993 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d273994 q = 1) (hb : d275715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d273994, d275715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d273994, d275715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d273995 q = 1) (hb : d275716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d273995, d275716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d273995, d275716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d273996 q = 1) (hb : d275717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d273996, d275717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d273996, d275717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d273997 q = 1) (hb : d275718 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d273997, d275718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d273997, d275718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro69505 (p : Pattern) (ha : d274006 p = 1) (hb : d277242 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d273989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d273850 q = 1) (hb : d275651 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d273850, d275651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69164 q ha hb
    | true =>
      simp only [d273850, d275651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69144 q ha hb
  have h3 (q : Pattern) (ha : d273990 q = 1) (hb : d275714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d273990, d275714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d273990, d275714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d273993 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d273994 q = 1) (hb : d275715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d273994, d275715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d273994, d275715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d274004 q = 1) (hb : d275716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d274004, d275716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274004, d275716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d274005 q = 1) (hb : d275717 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d274005, d275717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274005, d275717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d274006 q = 1) (hb : d277242 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d274006, d277242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274006, d277242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69506 (p : Pattern) (ha : d274048 p = 1) (hb : d277252 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d274037 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d273888 q = 1) (hb : d275689 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d273888, d275689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69170 q ha hb
    | true =>
      simp only [d273888, d275689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69149 q ha hb
  have h3 (q : Pattern) (ha : d274038 q = 1) (hb : d277248 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d274038, d277248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d274038, d277248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d274044 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d274045 q = 1) (hb : d277249 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d274045, d277249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d274045, d277249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d274046 q = 1) (hb : d277250 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d274046, d277250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274046, d277250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d274047 q = 1) (hb : d277251 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d274047, d277251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274047, d277251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d274048 q = 1) (hb : d277252 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d274048, d277252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274048, d277252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69507 (p : Pattern) (ha : d274060 p = 1) (hb : d277258 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d273920 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d273998 q = 1) (hb : d275719 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d273998, d275719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69503 q ha hb
    | true =>
      simp only [d273998, d275719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69504 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d274000 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d274001 q = 1) (hb : d275720 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d274001, d275720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d274001, d275720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d274002 q = 1) (hb : d277240 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d274002, d277240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d274002, d277240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d274003 q = 1) (hb : d277241 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d274003, d277241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274003, d277241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d274007 q = 1) (hb : d277243 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d274007, d277243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d274007, d277243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69505 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d274009 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d274010 q = 1) (hb : d277244 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d274010, d277244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d274010, d277244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d274011 q = 1) (hb : d277245 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d274011, d277245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d274011, d277245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d274012 q = 1) (hb : d277246 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d274012, d277246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d274012, d277246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d274013 q = 1) (hb : d277247 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d274013, d277247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d274013, d277247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d274049 q = 1) (hb : d277253 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d274049, d277253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d274049, d277253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69506 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d274055 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d274056 q = 1) (hb : d277254 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d274056, d277254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d274056, d277254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d274057 q = 1) (hb : d277255 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d274057, d277255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d274057, d277255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d274058 q = 1) (hb : d277256 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d274058, d277256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d274058, d277256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d274059 q = 1) (hb : d277257 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d274059, d277257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d274059, d277257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d274060 q = 1) (hb : d277258 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d274060, d277258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d274060, d277258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro69508 (p : Pattern) (ha : d274066 p = 1) (hb : d277264 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d274061 q = 1) (hb : d277259 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d274061, d277259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274061, d277259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69507 q ha hb
  have h2 (q : Pattern) (ha : d274062 q = 1) (hb : d277260 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d274062, d277260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274062, d277260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d274063 q = 1) (hb : d277261 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d274063, d277261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274063, d277261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d274064 q = 1) (hb : d277262 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d274064, d277262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274064, d277262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d274065 q = 1) (hb : d277263 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d274065, d277263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274065, d277263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d274066 q = 1) (hb : d277264 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d274066, d277264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274066, d277264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69509 (p : Pattern) (ha : d274182 p = 1) (hb : d275906 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d274111 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d274120 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d274171 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d274085 q = 1) (hb : d275901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d274085, d275901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69206 q ha hb
    | true =>
      simp only [d274085, d275901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69207 q ha hb
  have h5 (q : Pattern) (ha : d274172 q = 1) (hb : d275902 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d274172, d275902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d274172, d275902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d274178 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d274179 q = 1) (hb : d275903 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d274179, d275903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d274179, d275903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d274180 q = 1) (hb : d275904 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d274180, d275904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d274180, d275904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d274181 q = 1) (hb : d275905 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d274181, d275905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d274181, d275905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d274182 q = 1) (hb : d275906 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d274182, d275906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274182, d275906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro69510 (p : Pattern) (ha : d274203 p = 1) (hb : d275916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d274111 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d274120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d274171 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d274085 q = 1) (hb : d275901 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d274085, d275901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69206 q ha hb
    | true =>
      simp only [d274085, d275901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69207 q ha hb
  have h4 (q : Pattern) (ha : d274172 q = 1) (hb : d275902 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d274172, d275902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d274172, d275902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d274178 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d274179 q = 1) (hb : d275903 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d274179, d275903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d274179, d275903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d274180 q = 1) (hb : d275904 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d274180, d275904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d274180, d275904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d274181 q = 1) (hb : d275905 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d274181, d275905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274181, d275905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d274188 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d274193 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d274195 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d274095 q = 1) (hb : d275911 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d274095, d275911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69209 q ha hb
    | true =>
      simp only [d274095, d275911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69210 q ha hb
  have h13 (q : Pattern) (ha : d274196 q = 1) (hb : d275912 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d274196, d275912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d274196, d275912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d274199 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d274200 q = 1) (hb : d275913 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d274200, d275913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d274200, d275913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d274201 q = 1) (hb : d275914 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d274201, d275914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d274201, d275914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d274202 q = 1) (hb : d275915 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d274202, d275915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d274202, d275915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d274203 q = 1) (hb : d275916 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d274203, d275916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d274203, d275916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro69511 (p : Pattern) (ha : d274223 p = 1) (hb : d277268 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d274195 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d274095 q = 1) (hb : d275911 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d274095, d275911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69209 q ha hb
    | true =>
      simp only [d274095, d275911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69210 q ha hb
  have h3 (q : Pattern) (ha : d274196 q = 1) (hb : d275912 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d274196, d275912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d274196, d275912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d274199 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d274200 q = 1) (hb : d275913 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d274200, d275913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d274200, d275913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d274221 q = 1) (hb : d275914 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d274221, d275914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274221, d275914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d274222 q = 1) (hb : d275915 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d274222, d275915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274222, d275915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d274223 q = 1) (hb : d277268 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d274223, d277268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274223, d277268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69512 (p : Pattern) (ha : d274291 p = 1) (hb : d277279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d274275 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d274280 q = 1) (hb : d277274 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d274280, d277274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69244 q ha hb
    | true =>
      simp only [d274280, d277274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69247 q ha hb
  have h3 (q : Pattern) (ha : d274281 q = 1) (hb : d277275 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d274281, d277275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d274281, d277275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d274287 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d274288 q = 1) (hb : d277276 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d274288, d277276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d274288, d277276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d274289 q = 1) (hb : d277277 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d274289, d277277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274289, d277277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d274290 q = 1) (hb : d277278 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d274290, d277278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274290, d277278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d274291 q = 1) (hb : d277279 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d274291, d277279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274291, d277279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69513 (p : Pattern) (ha : d274304 p = 1) (hb : d277285 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d274103 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d274204 q = 1) (hb : d275917 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d274204, d275917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69509 q ha hb
    | true =>
      simp only [d274204, d275917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69510 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d274217 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d274218 q = 1) (hb : d275918 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d274218, d275918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d274218, d275918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d274219 q = 1) (hb : d277266 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d274219, d277266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d274219, d277266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d274220 q = 1) (hb : d277267 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d274220, d277267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274220, d277267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d274224 q = 1) (hb : d277269 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d274224, d277269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d274224, d277269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69511 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d274226 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d274227 q = 1) (hb : d277270 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d274227, d277270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d274227, d277270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d274228 q = 1) (hb : d277271 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d274228, d277271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d274228, d277271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d274229 q = 1) (hb : d277272 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d274229, d277272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d274229, d277272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d274230 q = 1) (hb : d277273 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d274230, d277273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d274230, d277273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d274292 q = 1) (hb : d277280 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d274292, d277280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d274292, d277280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69512 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d274299 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d274300 q = 1) (hb : d277281 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d274300, d277281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d274300, d277281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d274301 q = 1) (hb : d277282 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d274301, d277282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d274301, d277282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d274302 q = 1) (hb : d277283 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d274302, d277283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d274302, d277283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d274303 q = 1) (hb : d277284 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d274303, d277284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d274303, d277284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d274304 q = 1) (hb : d277285 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d274304, d277285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d274304, d277285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro69514 (p : Pattern) (ha : d274310 p = 1) (hb : d277291 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d274305 q = 1) (hb : d277286 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d274305, d277286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274305, d277286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69513 q ha hb
  have h2 (q : Pattern) (ha : d274306 q = 1) (hb : d277287 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d274306, d277287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274306, d277287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d274307 q = 1) (hb : d277288 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d274307, d277288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274307, d277288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d274308 q = 1) (hb : d277289 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d274308, d277289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274308, d277289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d274309 q = 1) (hb : d277290 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d274309, d277290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274309, d277290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d274310 q = 1) (hb : d277291 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d274310, d277291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274310, d277291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69515 (p : Pattern) (ha : d274438 p = 1) (hb : d276171 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d274374 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d274383 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d274427 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d274348 q = 1) (hb : d276166 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d274348, d276166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69259 q ha hb
    | true =>
      simp only [d274348, d276166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69260 q ha hb
  have h5 (q : Pattern) (ha : d274428 q = 1) (hb : d276167 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d274428, d276167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d274428, d276167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d274434 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d274435 q = 1) (hb : d276168 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d274435, d276168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d274435, d276168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d274436 q = 1) (hb : d276169 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d274436, d276169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d274436, d276169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d274437 q = 1) (hb : d276170 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d274437, d276170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d274437, d276170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d274438 q = 1) (hb : d276171 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d274438, d276171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274438, d276171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro69516 (p : Pattern) (ha : d274459 p = 1) (hb : d276181 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d274374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d274383 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d274427 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d274348 q = 1) (hb : d276166 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d274348, d276166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69259 q ha hb
    | true =>
      simp only [d274348, d276166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69260 q ha hb
  have h4 (q : Pattern) (ha : d274428 q = 1) (hb : d276167 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d274428, d276167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d274428, d276167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d274434 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d274435 q = 1) (hb : d276168 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d274435, d276168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d274435, d276168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d274436 q = 1) (hb : d276169 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d274436, d276169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d274436, d276169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d274437 q = 1) (hb : d276170 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d274437, d276170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274437, d276170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d274444 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d274449 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d274451 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d274358 q = 1) (hb : d276176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d274358, d276176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69262 q ha hb
    | true =>
      simp only [d274358, d276176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69263 q ha hb
  have h13 (q : Pattern) (ha : d274452 q = 1) (hb : d276177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d274452, d276177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d274452, d276177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d274455 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d274456 q = 1) (hb : d276178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d274456, d276178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d274456, d276178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d274457 q = 1) (hb : d276179 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d274457, d276179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d274457, d276179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d274458 q = 1) (hb : d276180 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d274458, d276180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d274458, d276180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d274459 q = 1) (hb : d276181 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d274459, d276181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d274459, d276181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro69517 (p : Pattern) (ha : d274479 p = 1) (hb : d277296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d274451 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d274358 q = 1) (hb : d276176 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d274358, d276176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69262 q ha hb
    | true =>
      simp only [d274358, d276176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69263 q ha hb
  have h3 (q : Pattern) (ha : d274452 q = 1) (hb : d276177 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d274452, d276177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d274452, d276177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d274455 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d274456 q = 1) (hb : d276178 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d274456, d276178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d274456, d276178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d274477 q = 1) (hb : d276179 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d274477, d276179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274477, d276179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d274478 q = 1) (hb : d276180 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d274478, d276180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274478, d276180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d274479 q = 1) (hb : d277296 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d274479, d277296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274479, d277296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69518 (p : Pattern) (ha : d274547 p = 1) (hb : d277305 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d274534 q = 1) (hb : d276388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d274534, d276388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69303 q ha hb
    | true =>
      simp only [d274534, d276388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d274535 q = 1) (hb : d276389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d274535, d276389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274535, d276389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d274542 q = 1) (hb : d276378 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d274542, d276378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69301 q ha hb
    | true =>
      simp only [d274542, d276378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d274543 q = 1) (hb : d276379 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d274543, d276379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274543, d276379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d274544 q = 1) (hb : d277302 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d274544, d277302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d274544, d277302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d274545 q = 1) (hb : d277303 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d274545, d277303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d274545, d277303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d274546 q = 1) (hb : d277304 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d274546, d277304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d274546, d277304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d274547 q = 1) (hb : d277305 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d274547, d277305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d274547, d277305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro69519 (p : Pattern) (ha : d274564 p = 1) (hb : d277311 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d274548 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d274553 q = 1) (hb : d277306 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d274553, d277306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69518 q ha hb
    | true =>
      simp only [d274553, d277306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69306 q ha hb
  have h3 (q : Pattern) (ha : d274554 q = 1) (hb : d277307 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d274554, d277307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d274554, d277307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d274560 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d274561 q = 1) (hb : d277308 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d274561, d277308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d274561, d277308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d274562 q = 1) (hb : d277309 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d274562, d277309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274562, d277309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d274563 q = 1) (hb : d277310 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d274563, d277310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274563, d277310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d274564 q = 1) (hb : d277311 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d274564, d277311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274564, d277311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69520 (p : Pattern) (ha : d274577 p = 1) (hb : d277317 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d274366 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d274460 q = 1) (hb : d276182 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d274460, d276182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69515 q ha hb
    | true =>
      simp only [d274460, d276182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69516 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d274473 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d274474 q = 1) (hb : d276183 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d274474, d276183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d274474, d276183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d274475 q = 1) (hb : d277294 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d274475, d277294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d274475, d277294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d274476 q = 1) (hb : d277295 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d274476, d277295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274476, d277295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d274480 q = 1) (hb : d277297 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d274480, d277297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d274480, d277297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69517 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d274482 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d274483 q = 1) (hb : d277298 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d274483, d277298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d274483, d277298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d274484 q = 1) (hb : d277299 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d274484, d277299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d274484, d277299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d274485 q = 1) (hb : d277300 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d274485, d277300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d274485, d277300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d274486 q = 1) (hb : d277301 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d274486, d277301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d274486, d277301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d274565 q = 1) (hb : d277312 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d274565, d277312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d274565, d277312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69519 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d274572 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d274573 q = 1) (hb : d277313 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d274573, d277313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d274573, d277313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d274574 q = 1) (hb : d277314 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d274574, d277314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d274574, d277314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d274575 q = 1) (hb : d277315 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d274575, d277315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d274575, d277315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d274576 q = 1) (hb : d277316 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d274576, d277316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d274576, d277316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d274577 q = 1) (hb : d277317 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d274577, d277317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d274577, d277317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro69521 (p : Pattern) (ha : d274583 p = 1) (hb : d277323 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d274578 q = 1) (hb : d277318 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d274578, d277318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274578, d277318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69520 q ha hb
  have h2 (q : Pattern) (ha : d274579 q = 1) (hb : d277319 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d274579, d277319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274579, d277319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d274580 q = 1) (hb : d277320 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d274580, d277320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274580, d277320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d274581 q = 1) (hb : d277321 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d274581, d277321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274581, d277321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d274582 q = 1) (hb : d277322 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d274582, d277322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274582, d277322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d274583 q = 1) (hb : d277323 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d274583, d277323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274583, d277323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69522 (p : Pattern) (ha : d274815 p = 1) (hb : d276535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d274736 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d274745 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d274795 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d274710 q = 1) (hb : d276530 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d274710, d276530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69327 q ha hb
    | true =>
      simp only [d274710, d276530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69328 q ha hb
  have h5 (q : Pattern) (ha : d274796 q = 1) (hb : d276531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d274796, d276531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d274796, d276531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d274811 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d274812 q = 1) (hb : d276532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d274812, d276532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d274812, d276532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d274813 q = 1) (hb : d276533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d274813, d276533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d274813, d276533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d274814 q = 1) (hb : d276534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d274814, d276534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d274814, d276534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d274815 q = 1) (hb : d276535 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d274815, d276535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274815, d276535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro69523 (p : Pattern) (ha : d274837 p = 1) (hb : d276545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d274736 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d274745 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d274795 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d274710 q = 1) (hb : d276530 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d274710, d276530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69327 q ha hb
    | true =>
      simp only [d274710, d276530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69328 q ha hb
  have h4 (q : Pattern) (ha : d274796 q = 1) (hb : d276531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d274796, d276531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d274796, d276531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d274811 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d274812 q = 1) (hb : d276532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d274812, d276532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d274812, d276532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d274813 q = 1) (hb : d276533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d274813, d276533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d274813, d276533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d274814 q = 1) (hb : d276534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d274814, d276534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274814, d276534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d274821 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d274826 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d274829 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d274720 q = 1) (hb : d276540 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d274720, d276540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69330 q ha hb
    | true =>
      simp only [d274720, d276540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69331 q ha hb
  have h13 (q : Pattern) (ha : d274830 q = 1) (hb : d276541 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d274830, d276541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d274830, d276541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d274833 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d274834 q = 1) (hb : d276542 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d274834, d276542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d274834, d276542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d274835 q = 1) (hb : d276543 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d274835, d276543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d274835, d276543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d274836 q = 1) (hb : d276544 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d274836, d276544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d274836, d276544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d274837 q = 1) (hb : d276545 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d274837, d276545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d274837, d276545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro69524 (p : Pattern) (ha : d274862 p = 1) (hb : d277329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d274829 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d274720 q = 1) (hb : d276540 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d274720, d276540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69330 q ha hb
    | true =>
      simp only [d274720, d276540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69331 q ha hb
  have h3 (q : Pattern) (ha : d274830 q = 1) (hb : d276541 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d274830, d276541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d274830, d276541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d274833 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d274834 q = 1) (hb : d276542 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d274834, d276542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d274834, d276542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d274860 q = 1) (hb : d276543 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d274860, d276543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274860, d276543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d274861 q = 1) (hb : d276544 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d274861, d276544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274861, d276544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d274862 q = 1) (hb : d277329 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d274862, d277329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274862, d277329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69525 (p : Pattern) (ha : d274971 p = 1) (hb : d277336 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d274924 q = 1) (hb : d276728 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d274924, d276728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69363 q ha hb
    | true =>
      simp only [d274924, d276728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69365 q ha hb
  have h2 (q : Pattern) (ha : d274925 q = 1) (hb : d276729 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d274925, d276729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274925, d276729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d274926 q = 1) (hb : d276730 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d274926, d276730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274926, d276730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d274938 q = 1) (hb : d276737 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d274938, d276737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69365 q ha hb
    | true =>
      simp only [d274938, d276737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69366 q ha hb
  have h5 (q : Pattern) (ha : d274939 q = 1) (hb : d276738 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d274939, d276738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274939, d276738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d274940 q = 1) (hb : d276739 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d274940, d276739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274940, d276739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d274941 q = 1) (hb : d276740 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d274941, d276740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d274941, d276740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d274957 q = 1) (hb : d276760 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d274957, d276760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69365 q ha hb
    | true =>
      simp only [d274957, d276760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69370 q ha hb
  have h9 (q : Pattern) (ha : d274958 q = 1) (hb : d276761 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d274958, d276761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274958, d276761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d274959 q = 1) (hb : d276762 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d274959, d276762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274959, d276762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d274960 q = 1) (hb : d276763 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d274960, d276763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d274960, d276763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d274970 q = 1) (hb : d277335 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d274970, d277335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d274970, d277335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d274971 q = 1) (hb : d277336 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d274971, d277336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d274971, d277336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro69526 (p : Pattern) (ha : d274977 p = 1) (hb : d277342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d274972 q = 1) (hb : d277337 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d274972, d277337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69525 q ha hb
    | true =>
      simp only [d274972, d277337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d274973 q = 1) (hb : d277338 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d274973, d277338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274973, d277338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d274963 q = 1) (hb : d276766 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d274963, d276766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69371 q ha hb
    | true =>
      simp only [d274963, d276766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d274964 q = 1) (hb : d276767 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d274964, d276767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274964, d276767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d274974 q = 1) (hb : d277339 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d274974, d277339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d274974, d277339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d274975 q = 1) (hb : d277340 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d274975, d277340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d274975, d277340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d274976 q = 1) (hb : d277341 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d274976, d277341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d274976, d277341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d274977 q = 1) (hb : d277342 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d274977, d277342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d274977, d277342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro69527 (p : Pattern) (ha : d275002 p = 1) (hb : d277348 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d274969 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d274982 q = 1) (hb : d277343 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d274982, d277343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69526 q ha hb
    | true =>
      simp only [d274982, d277343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69377 q ha hb
  have h3 (q : Pattern) (ha : d274983 q = 1) (hb : d277344 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d274983, d277344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d274983, d277344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d274998 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d274999 q = 1) (hb : d277345 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d274999, d277345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d274999, d277345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d275000 q = 1) (hb : d277346 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d275000, d277346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275000, d277346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d275001 q = 1) (hb : d277347 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d275001, d277347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275001, d277347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d275002 q = 1) (hb : d277348 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d275002, d277348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275002, d277348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69528 (p : Pattern) (ha : d275015 p = 1) (hb : d277354 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d274728 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d274838 q = 1) (hb : d276546 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d274838, d276546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69522 q ha hb
    | true =>
      simp only [d274838, d276546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69523 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d274856 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d274857 q = 1) (hb : d276547 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d274857, d276547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d274857, d276547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d274858 q = 1) (hb : d277327 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d274858, d277327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d274858, d277327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d274859 q = 1) (hb : d277328 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d274859, d277328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d274859, d277328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d274863 q = 1) (hb : d277330 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d274863, d277330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d274863, d277330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69524 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d274865 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d274866 q = 1) (hb : d277331 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d274866, d277331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d274866, d277331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d274867 q = 1) (hb : d277332 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d274867, d277332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d274867, d277332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d274868 q = 1) (hb : d277333 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d274868, d277333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d274868, d277333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d274869 q = 1) (hb : d277334 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d274869, d277334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d274869, d277334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d275003 q = 1) (hb : d277349 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d275003, d277349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d275003, d277349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69527 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d275010 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d275011 q = 1) (hb : d277350 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d275011, d277350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d275011, d277350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d275012 q = 1) (hb : d277351 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d275012, d277351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d275012, d277351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d275013 q = 1) (hb : d277352 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d275013, d277352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d275013, d277352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d275014 q = 1) (hb : d277353 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d275014, d277353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d275014, d277353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d275015 q = 1) (hb : d277354 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d275015, d277354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d275015, d277354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro69529 (p : Pattern) (ha : d275021 p = 1) (hb : d277360 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d275016 q = 1) (hb : d277355 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d275016, d277355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275016, d277355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69528 q ha hb
  have h2 (q : Pattern) (ha : d275017 q = 1) (hb : d277356 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d275017, d277356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275017, d277356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d275018 q = 1) (hb : d277357 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d275018, d277357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275018, d277357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d275019 q = 1) (hb : d277358 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d275019, d277358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275019, d277358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d275020 q = 1) (hb : d277359 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d275020, d277359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275020, d277359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d275021 q = 1) (hb : d277360 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d275021, d277360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275021, d277360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69530 (p : Pattern) (ha : d275249 p = 1) (hb : d276922 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d275175 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d275184 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d275212 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d275149 q = 1) (hb : d276917 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d275149, d276917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69397 q ha hb
    | true =>
      simp only [d275149, d276917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69398 q ha hb
  have h5 (q : Pattern) (ha : d275213 q = 1) (hb : d276918 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d275213, d276918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d275213, d276918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d275245 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d275246 q = 1) (hb : d276919 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d275246, d276919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d275246, d276919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d275247 q = 1) (hb : d276920 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d275247, d276920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d275247, d276920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d275248 q = 1) (hb : d276921 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d275248, d276921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d275248, d276921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d275249 q = 1) (hb : d276922 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d275249, d276922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275249, d276922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro69531 (p : Pattern) (ha : d275271 p = 1) (hb : d276932 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d275175 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d275184 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d275212 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d275149 q = 1) (hb : d276917 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d275149, d276917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69397 q ha hb
    | true =>
      simp only [d275149, d276917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69398 q ha hb
  have h4 (q : Pattern) (ha : d275213 q = 1) (hb : d276918 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d275213, d276918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d275213, d276918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d275245 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d275246 q = 1) (hb : d276919 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d275246, d276919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d275246, d276919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d275247 q = 1) (hb : d276920 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d275247, d276920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d275247, d276920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d275248 q = 1) (hb : d276921 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d275248, d276921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275248, d276921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d275255 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d275260 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d275263 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d275159 q = 1) (hb : d276927 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d275159, d276927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69400 q ha hb
    | true =>
      simp only [d275159, d276927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69401 q ha hb
  have h13 (q : Pattern) (ha : d275264 q = 1) (hb : d276928 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d275264, d276928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d275264, d276928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d275267 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d275268 q = 1) (hb : d276929 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d275268, d276929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d275268, d276929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d275269 q = 1) (hb : d276930 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d275269, d276930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d275269, d276930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d275270 q = 1) (hb : d276931 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d275270, d276931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d275270, d276931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d275271 q = 1) (hb : d276932 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d275271, d276932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d275271, d276932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro69532 (p : Pattern) (ha : d275296 p = 1) (hb : d277367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d275263 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d275159 q = 1) (hb : d276927 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d275159, d276927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69400 q ha hb
    | true =>
      simp only [d275159, d276927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69401 q ha hb
  have h3 (q : Pattern) (ha : d275264 q = 1) (hb : d276928 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d275264, d276928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d275264, d276928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d275267 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d275268 q = 1) (hb : d276929 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d275268, d276929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d275268, d276929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d275294 q = 1) (hb : d276930 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d275294, d276930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275294, d276930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d275295 q = 1) (hb : d276931 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d275295, d276931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275295, d276931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d275296 q = 1) (hb : d277367 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d275296, d277367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275296, d277367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69533 (p : Pattern) (ha : d275391 p = 1) (hb : d277374 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d275344 q = 1) (hb : d277087 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d275344, d277087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69431 q ha hb
    | true =>
      simp only [d275344, d277087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69433 q ha hb
  have h2 (q : Pattern) (ha : d275345 q = 1) (hb : d277088 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d275345, d277088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275345, d277088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d275346 q = 1) (hb : d277089 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d275346, d277089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275346, d277089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d275358 q = 1) (hb : d277096 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d275358, d277096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69433 q ha hb
    | true =>
      simp only [d275358, d277096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69434 q ha hb
  have h5 (q : Pattern) (ha : d275359 q = 1) (hb : d277097 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d275359, d277097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275359, d277097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d275360 q = 1) (hb : d277098 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d275360, d277098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275360, d277098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d275361 q = 1) (hb : d277099 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d275361, d277099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d275361, d277099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d275377 q = 1) (hb : d277119 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d275377, d277119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69433 q ha hb
    | true =>
      simp only [d275377, d277119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69438 q ha hb
  have h9 (q : Pattern) (ha : d275378 q = 1) (hb : d277120 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d275378, d277120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275378, d277120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d275379 q = 1) (hb : d277121 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d275379, d277121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275379, d277121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d275380 q = 1) (hb : d277122 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d275380, d277122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d275380, d277122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d275390 q = 1) (hb : d277373 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d275390, d277373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d275390, d277373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d275391 q = 1) (hb : d277374 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d275391, d277374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d275391, d277374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro69534 (p : Pattern) (ha : d275397 p = 1) (hb : d277380 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d275392 q = 1) (hb : d277375 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d275392, d277375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69533 q ha hb
    | true =>
      simp only [d275392, d277375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d275393 q = 1) (hb : d277376 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d275393, d277376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275393, d277376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d275383 q = 1) (hb : d277125 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d275383, d277125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69439 q ha hb
    | true =>
      simp only [d275383, d277125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d275384 q = 1) (hb : d277126 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d275384, d277126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275384, d277126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d275394 q = 1) (hb : d277377 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d275394, d277377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d275394, d277377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d275395 q = 1) (hb : d277378 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d275395, d277378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d275395, d277378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d275396 q = 1) (hb : d277379 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d275396, d277379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d275396, d277379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d275397 q = 1) (hb : d277380 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d275397, d277380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d275397, d277380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro69535 (p : Pattern) (ha : d275433 p = 1) (hb : d277386 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d275389 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d275402 q = 1) (hb : d277381 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d275402, d277381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69534 q ha hb
    | true =>
      simp only [d275402, d277381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69446 q ha hb
  have h3 (q : Pattern) (ha : d275403 q = 1) (hb : d277382 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d275403, d277382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d275403, d277382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d275429 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d275430 q = 1) (hb : d277383 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d275430, d277383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d275430, d277383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d275431 q = 1) (hb : d277384 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d275431, d277384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275431, d277384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d275432 q = 1) (hb : d277385 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d275432, d277385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275432, d277385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d275433 q = 1) (hb : d277386 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d275433, d277386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275433, d277386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69536 (p : Pattern) (ha : d275446 p = 1) (hb : d277392 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d275167 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d275272 q = 1) (hb : d276933 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d275272, d276933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69530 q ha hb
    | true =>
      simp only [d275272, d276933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69531 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d275290 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d275291 q = 1) (hb : d276934 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d275291, d276934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275291, d276934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d275292 q = 1) (hb : d277365 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d275292, d277365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d275292, d277365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d275293 q = 1) (hb : d277366 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d275293, d277366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275293, d277366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d275297 q = 1) (hb : d277368 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d275297, d277368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d275297, d277368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69532 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d275299 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d275300 q = 1) (hb : d277369 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d275300, d277369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d275300, d277369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d275301 q = 1) (hb : d277370 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d275301, d277370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d275301, d277370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d275302 q = 1) (hb : d277371 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d275302, d277371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d275302, d277371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d275303 q = 1) (hb : d277372 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d275303, d277372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d275303, d277372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d275434 q = 1) (hb : d277387 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d275434, d277387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d275434, d277387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69535 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d275441 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d275442 q = 1) (hb : d277388 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d275442, d277388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d275442, d277388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d275443 q = 1) (hb : d277389 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d275443, d277389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d275443, d277389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d275444 q = 1) (hb : d277390 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d275444, d277390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d275444, d277390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d275445 q = 1) (hb : d277391 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d275445, d277391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d275445, d277391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d275446 q = 1) (hb : d277392 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d275446, d277392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d275446, d277392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro69537 (p : Pattern) (ha : d275452 p = 1) (hb : d277398 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d275447 q = 1) (hb : d277393 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d275447, d277393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275447, d277393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69536 q ha hb
  have h2 (q : Pattern) (ha : d275448 q = 1) (hb : d277394 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d275448, d277394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275448, d277394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d275449 q = 1) (hb : d277395 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d275449, d277395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275449, d277395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d275450 q = 1) (hb : d277396 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d275450, d277396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275450, d277396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d275451 q = 1) (hb : d277397 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d275451, d277397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275451, d277397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d275452 q = 1) (hb : d277398 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d275452, d277398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d275452, d277398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69538 (p : Pattern) (ha : d275458 p = 1) (hb : d277404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d274067 q = 1) (hb : d277265 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d274067, d277265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69502 q ha hb
    | true =>
      simp only [d274067, d277265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69508 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d274311 q = 1) (hb : d277292 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d274311, d277292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d274311, d277292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69514 q ha hb
  have h3 (q : Pattern) (ha : d274312 q = 1) (hb : d277293 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d274312, d277293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d274312, d277293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d274584 q = 1) (hb : d277324 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d274584, d277324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d274584, d277324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69521 q ha hb
  have h5 (q : Pattern) (ha : d274585 q = 1) (hb : d277325 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d274585, d277325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d274585, d277325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d274586 q = 1) (hb : d277326 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d274586, d277326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d274586, d277326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d275022 q = 1) (hb : d277361 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d275022, d277361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d275022, d277361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69529 q ha hb
  have h8 (q : Pattern) (ha : d275023 q = 1) (hb : d277362 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d275023, d277362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d275023, d277362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d275024 q = 1) (hb : d277363 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d275024, d277363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d275024, d277363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d275025 q = 1) (hb : d277364 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d275025, d277364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d275025, d277364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d275453 q = 1) (hb : d277399 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d275453, d277399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d275453, d277399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69537 q ha hb
  have h12 (q : Pattern) (ha : d275454 q = 1) (hb : d277400 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d275454, d277400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d275454, d277400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d275455 q = 1) (hb : d277401 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d275455, d277401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d275455, d277401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d275456 q = 1) (hb : d277402 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d275456, d277402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d275456, d277402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d275457 q = 1) (hb : d277403 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d275457, d277403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d275457, d277403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d275458 q = 1) (hb : d277404 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d275458, d277404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d275458, d277404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro69539 (p : Pattern) (ha : d275464 p = 1) (hb : d277410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d275459 q = 1) (hb : d277405 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d275459, d277405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69538 q ha hb
    | true =>
      simp only [d275459, d277405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d275460 q = 1) (hb : d277406 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d275460, d277406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275460, d277406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d275461 q = 1) (hb : d277407 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d275461, d277407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d275461, d277407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d275462 q = 1) (hb : d277408 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d275462, d277408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d275462, d277408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d275463 q = 1) (hb : d277409 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d275463, d277409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d275463, d277409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d275464 q = 1) (hb : d277410 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d275464, d277410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d275464, d277410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro69540 (p : Pattern) (ha : d275470 p = 1) (hb : d277416 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d275465 q = 1) (hb : d277411 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d275465, d277411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69539 q ha hb
    | true =>
      simp only [d275465, d277411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d275466 q = 1) (hb : d277412 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d275466, d277412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275466, d277412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d275467 q = 1) (hb : d277413 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d275467, d277413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d275467, d277413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d275468 q = 1) (hb : d277414 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d275468, d277414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d275468, d277414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d275469 q = 1) (hb : d277415 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d275469, d277415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d275469, d277415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d275470 q = 1) (hb : d277416 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d275470, d277416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d275470, d277416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro69541 (p : Pattern) (ha : d275476 p = 1) (hb : d277422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d275471 q = 1) (hb : d277417 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d275471, d277417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69540 q ha hb
    | true =>
      simp only [d275471, d277417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d275472 q = 1) (hb : d277418 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d275472, d277418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275472, d277418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d275473 q = 1) (hb : d277419 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d275473, d277419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d275473, d277419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d275474 q = 1) (hb : d277420 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d275474, d277420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d275474, d277420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d275475 q = 1) (hb : d277421 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d275475, d277421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d275475, d277421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d275476 q = 1) (hb : d277422 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d275476, d277422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d275476, d277422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro69542 (p : Pattern) (ha : d275482 p = 1) (hb : d277428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d275477 q = 1) (hb : d277423 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d275477, d277423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69541 q ha hb
    | true =>
      simp only [d275477, d277423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d275478 q = 1) (hb : d277424 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d275478, d277424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275478, d277424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d275479 q = 1) (hb : d277425 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d275479, d277425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d275479, d277425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d275480 q = 1) (hb : d277426 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d275480, d277426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d275480, d277426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d275481 q = 1) (hb : d277427 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d275481, d277427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d275481, d277427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d275482 q = 1) (hb : d277428 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d275482, d277428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d275482, d277428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro69543 (p : Pattern) (ha : d275488 p = 1) (hb : d277434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d275483 q = 1) (hb : d277429 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d275483, d277429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69542 q ha hb
    | true =>
      simp only [d275483, d277429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d275484 q = 1) (hb : d277430 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d275484, d277430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275484, d277430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d275485 q = 1) (hb : d277431 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d275485, d277431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d275485, d277431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d275486 q = 1) (hb : d277432 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d275486, d277432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d275486, d277432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d275487 q = 1) (hb : d277433 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d275487, d277433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d275487, d277433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d275488 q = 1) (hb : d277434 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d275488, d277434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d275488, d277434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro69544 (p : Pattern) (ha : d275494 p = 1) (hb : d277440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d275489 q = 1) (hb : d277435 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d275489, d277435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69543 q ha hb
    | true =>
      simp only [d275489, d277435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d275490 q = 1) (hb : d277436 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d275490, d277436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275490, d277436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d275491 q = 1) (hb : d277437 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d275491, d277437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d275491, d277437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d275492 q = 1) (hb : d277438 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d275492, d277438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d275492, d277438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d275493 q = 1) (hb : d277439 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d275493, d277439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d275493, d277439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d275494 q = 1) (hb : d277440 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d275494, d277440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d275494, d277440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro69545 (p : Pattern) (ha : d275500 p = 1) (hb : d277446 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d275495 q = 1) (hb : d277441 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d275495, d277441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69544 q ha hb
    | true =>
      simp only [d275495, d277441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d275496 q = 1) (hb : d277442 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d275496, d277442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275496, d277442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d275497 q = 1) (hb : d277443 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d275497, d277443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d275497, d277443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d275498 q = 1) (hb : d277444 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d275498, d277444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d275498, d277444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d275499 q = 1) (hb : d277445 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d275499, d277445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d275499, d277445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d275500 q = 1) (hb : d277446 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d275500, d277446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d275500, d277446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro69546 (p : Pattern) (ha : d275585 p = 1) (hb : d277451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271319 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d271325 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d271354 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d275523 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d275581 q = 1) (hb : d277447 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d275581, d277447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d275581, d277447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d271242 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d275582 q = 1) (hb : d277448 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d275582, d277448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d275582, d277448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d275583 q = 1) (hb : d277449 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d275583, d277449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d275583, d277449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d275584 q = 1) (hb : d277450 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d275584, d277450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275584, d277450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d275585 q = 1) (hb : d277451 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d275585, d277451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d275585, d277451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro69547 (p : Pattern) (ha : d275592 p = 1) (hb : d277456 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271319 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271325 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d271354 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d275523 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d275581 q = 1) (hb : d277447 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d275581, d277447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d275581, d277447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d271242 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d275582 q = 1) (hb : d277448 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d275582, d277448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d275582, d277448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d275583 q = 1) (hb : d277449 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d275583, d277449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275583, d277449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d275584 q = 1) (hb : d277450 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d275584, d277450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d275584, d277450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d271393 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d271397 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d271399 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d275530 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d275588 q = 1) (hb : d277452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d275588, d277452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d275588, d277452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d271249 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d275589 q = 1) (hb : d277453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d275589, d277453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d275589, d277453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d275590 q = 1) (hb : d277454 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d275590, d277454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d275590, d277454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d275591 q = 1) (hb : d277455 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d275591, d277455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d275591, d277455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d275592 q = 1) (hb : d277456 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d275592, d277456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d275592, d277456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro69548 (p : Pattern) (ha : d275820 p = 1) (hb : d277463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271399 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d275530 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d275588 q = 1) (hb : d277452 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d275588, d277452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275588, d277452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d271249 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d275589 q = 1) (hb : d277453 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d275589, d277453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d275589, d277453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d275590 q = 1) (hb : d277461 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d275590, d277461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d275590, d277461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d275591 q = 1) (hb : d277462 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d275591, d277462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d275591, d277462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d275820 q = 1) (hb : d277463 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d275820, d277463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d275820, d277463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69549 (p : Pattern) (ha : d275870 p = 1) (hb : d277473 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271439 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d275564 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d275866 q = 1) (hb : d277469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d275866, d277469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275866, d277469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d271283 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d275867 q = 1) (hb : d277470 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d275867, d277470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d275867, d277470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d275868 q = 1) (hb : d277471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d275868, d277471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d275868, d277471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d275869 q = 1) (hb : d277472 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d275869, d277472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d275869, d277472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d275870 q = 1) (hb : d277473 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d275870, d277473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d275870, d277473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69550 (p : Pattern) (ha : d277233 p = 1) (hb : d277479 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271313 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d275593 q = 1) (hb : d277457 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d275593, d277457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69546 q ha hb
    | true =>
      simp only [d275593, d277457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69547 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d271409 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d275594 q = 1) (hb : d277458 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d275594, d277458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275594, d277458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d277223 q = 1) (hb : d277459 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d277223, d277459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d277223, d277459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d277224 q = 1) (hb : d277460 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d277224, d277460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277224, d277460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d275821 q = 1) (hb : d277464 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d275821, d277464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d275821, d277464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69548 q ha hb
  have h8 (q : Pattern) (ha : d277225 q = 1) (hb : d277465 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d277225, d277465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d277225, d277465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d277226 q = 1) (hb : d277466 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d277226, d277466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d277226, d277466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d277227 q = 1) (hb : d277467 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d277227, d277467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d277227, d277467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d277228 q = 1) (hb : d277468 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d277228, d277468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d277228, d277468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d275871 q = 1) (hb : d277474 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d275871, d277474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d275871, d277474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69549 q ha hb
  have h13 (q : Pattern) (ha : d277229 q = 1) (hb : d277475 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d277229, d277475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d277229, d277475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d277230 q = 1) (hb : d277476 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d277230, d277476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d277230, d277476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d277231 q = 1) (hb : d277477 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d277231, d277477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d277231, d277477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d277232 q = 1) (hb : d277478 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d277232, d277478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d277232, d277478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d277233 q = 1) (hb : d277479 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d277233, d277479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d277233, d277479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro69551 (p : Pattern) (ha : d277239 p = 1) (hb : d277485 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271298 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d277234 q = 1) (hb : d277480 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d277234, d277480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277234, d277480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69550 q ha hb
  have h3 (q : Pattern) (ha : d277235 q = 1) (hb : d277481 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d277235, d277481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277235, d277481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d277236 q = 1) (hb : d277482 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d277236, d277482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277236, d277482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d277237 q = 1) (hb : d277483 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d277237, d277483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277237, d277483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d277238 q = 1) (hb : d277484 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d277238, d277484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277238, d277484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d277239 q = 1) (hb : d277485 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d277239, d277485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277239, d277485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro69552 (p : Pattern) (ha : d275711 p = 1) (hb : d277490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271496 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d271502 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d271537 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d275635 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d275707 q = 1) (hb : d277486 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d275707, d277486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d275707, d277486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d271572 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d275708 q = 1) (hb : d277487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d275708, d277487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d275708, d277487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d275709 q = 1) (hb : d277488 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d275709, d277488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d275709, d277488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d275710 q = 1) (hb : d277489 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d275710, d277489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275710, d277489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d275711 q = 1) (hb : d277490 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d275711, d277490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d275711, d277490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro69553 (p : Pattern) (ha : d275718 p = 1) (hb : d277495 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271496 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271502 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d271537 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d275635 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d275707 q = 1) (hb : d277486 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d275707, d277486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d275707, d277486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d271572 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d275708 q = 1) (hb : d277487 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d275708, d277487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d275708, d277487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d275709 q = 1) (hb : d277488 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d275709, d277488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275709, d277488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d275710 q = 1) (hb : d277489 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d275710, d277489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d275710, d277489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d271581 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d271585 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d271587 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d275651 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d275714 q = 1) (hb : d277491 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d275714, d277491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d275714, d277491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d271593 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d275715 q = 1) (hb : d277492 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d275715, d277492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d275715, d277492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d275716 q = 1) (hb : d277493 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d275716, d277493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d275716, d277493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d275717 q = 1) (hb : d277494 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d275717, d277494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d275717, d277494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d275718 q = 1) (hb : d277495 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d275718, d277495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d275718, d277495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro69554 (p : Pattern) (ha : d277242 p = 1) (hb : d277502 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271587 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d275651 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d275714 q = 1) (hb : d277491 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d275714, d277491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275714, d277491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d271593 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d275715 q = 1) (hb : d277492 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d275715, d277492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d275715, d277492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d275716 q = 1) (hb : d277500 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d275716, d277500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d275716, d277500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d275717 q = 1) (hb : d277501 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d275717, d277501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d275717, d277501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d277242 q = 1) (hb : d277502 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d277242, d277502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277242, d277502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69555 (p : Pattern) (ha : d277252 p = 1) (hb : d277512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271637 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d275689 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d277248 q = 1) (hb : d277508 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d277248, d277508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277248, d277508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d271663 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d277249 q = 1) (hb : d277509 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d277249, d277509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d277249, d277509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d277250 q = 1) (hb : d277510 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d277250, d277510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277250, d277510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d277251 q = 1) (hb : d277511 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d277251, d277511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277251, d277511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d277252 q = 1) (hb : d277512 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d277252, d277512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277252, d277512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69556 (p : Pattern) (ha : d277258 p = 1) (hb : d277518 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271490 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d275719 q = 1) (hb : d277496 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d275719, d277496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69552 q ha hb
    | true =>
      simp only [d275719, d277496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69553 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d271600 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d275720 q = 1) (hb : d277497 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d275720, d277497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275720, d277497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d277240 q = 1) (hb : d277498 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d277240, d277498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d277240, d277498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d277241 q = 1) (hb : d277499 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d277241, d277499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277241, d277499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d277243 q = 1) (hb : d277503 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d277243, d277503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d277243, d277503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69554 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d271609 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d277244 q = 1) (hb : d277504 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d277244, d277504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d277244, d277504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d277245 q = 1) (hb : d277505 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d277245, d277505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d277245, d277505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d277246 q = 1) (hb : d277506 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d277246, d277506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d277246, d277506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d277247 q = 1) (hb : d277507 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d277247, d277507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d277247, d277507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d277253 q = 1) (hb : d277513 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d277253, d277513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d277253, d277513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69555 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d271674 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d277254 q = 1) (hb : d277514 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d277254, d277514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d277254, d277514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d277255 q = 1) (hb : d277515 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d277255, d277515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d277255, d277515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d277256 q = 1) (hb : d277516 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d277256, d277516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d277256, d277516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d277257 q = 1) (hb : d277517 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d277257, d277517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d277257, d277517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d277258 q = 1) (hb : d277518 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d277258, d277518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d277258, d277518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro69557 (p : Pattern) (ha : d277264 p = 1) (hb : d277524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d277259 q = 1) (hb : d277519 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d277259, d277519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277259, d277519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69556 q ha hb
  have h2 (q : Pattern) (ha : d277260 q = 1) (hb : d277520 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d277260, d277520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277260, d277520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d277261 q = 1) (hb : d277521 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d277261, d277521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277261, d277521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d277262 q = 1) (hb : d277522 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d277262, d277522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277262, d277522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d277263 q = 1) (hb : d277523 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d277263, d277523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277263, d277523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d277264 q = 1) (hb : d277524 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d277264, d277524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277264, d277524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69558 (p : Pattern) (ha : d275906 p = 1) (hb : d277530 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271730 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d271739 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d271790 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d275901 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d275902 q = 1) (hb : d277526 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d275902, d277526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d275902, d277526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d271841 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d275903 q = 1) (hb : d277527 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d275903, d277527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d275903, d277527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d275904 q = 1) (hb : d277528 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d275904, d277528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d275904, d277528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d275905 q = 1) (hb : d277529 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d275905, d277529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275905, d277529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d275906 q = 1) (hb : d277530 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d275906, d277530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d275906, d277530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro69559 (p : Pattern) (ha : d275916 p = 1) (hb : d277535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271730 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271739 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d271790 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d275901 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d275902 q = 1) (hb : d277526 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d275902, d277526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d275902, d277526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d271841 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d275903 q = 1) (hb : d277527 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d275903, d277527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d275903, d277527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d275904 q = 1) (hb : d277528 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d275904, d277528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275904, d277528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d275905 q = 1) (hb : d277529 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d275905, d277529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d275905, d277529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d271851 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d271856 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d271858 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d275911 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d275912 q = 1) (hb : d277531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d275912, d277531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d275912, d277531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d271865 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d275913 q = 1) (hb : d277532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d275913, d277532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d275913, d277532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d275914 q = 1) (hb : d277533 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d275914, d277533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d275914, d277533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d275915 q = 1) (hb : d277534 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d275915, d277534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d275915, d277534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d275916 q = 1) (hb : d277535 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d275916, d277535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d275916, d277535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro69560 (p : Pattern) (ha : d277268 p = 1) (hb : d277542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271858 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d275911 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d275912 q = 1) (hb : d277531 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d275912, d277531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275912, d277531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d271865 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d275913 q = 1) (hb : d277532 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d275913, d277532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d275913, d277532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d275914 q = 1) (hb : d277540 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d275914, d277540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d275914, d277540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d275915 q = 1) (hb : d277541 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d275915, d277541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d275915, d277541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d277268 q = 1) (hb : d277542 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d277268, d277542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277268, d277542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69561 (p : Pattern) (ha : d277279 p = 1) (hb : d277552 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d271941 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d277274 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d277275 q = 1) (hb : d277548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d277275, d277548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277275, d277548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d271981 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d277276 q = 1) (hb : d277549 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d277276, d277549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d277276, d277549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d277277 q = 1) (hb : d277550 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d277277, d277550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277277, d277550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d277278 q = 1) (hb : d277551 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d277278, d277551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277278, d277551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d277279 q = 1) (hb : d277552 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d277279, d277552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277279, d277552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69562 (p : Pattern) (ha : d277285 p = 1) (hb : d277558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d271722 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d275917 q = 1) (hb : d277536 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d275917, d277536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69558 q ha hb
    | true =>
      simp only [d275917, d277536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69559 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d271883 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d275918 q = 1) (hb : d277537 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d275918, d277537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d275918, d277537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d277266 q = 1) (hb : d277538 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d277266, d277538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d277266, d277538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d277267 q = 1) (hb : d277539 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d277267, d277539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277267, d277539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d277269 q = 1) (hb : d277543 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d277269, d277543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d277269, d277543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69560 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d271892 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d277270 q = 1) (hb : d277544 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d277270, d277544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d277270, d277544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d277271 q = 1) (hb : d277545 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d277271, d277545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d277271, d277545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d277272 q = 1) (hb : d277546 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d277272, d277546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d277272, d277546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d277273 q = 1) (hb : d277547 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d277273, d277547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d277273, d277547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d277280 q = 1) (hb : d277553 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d277280, d277553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d277280, d277553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69561 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d271997 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d277281 q = 1) (hb : d277554 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d277281, d277554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d277281, d277554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d277282 q = 1) (hb : d277555 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d277282, d277555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d277282, d277555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d277283 q = 1) (hb : d277556 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d277283, d277556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d277283, d277556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d277284 q = 1) (hb : d277557 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d277284, d277557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d277284, d277557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d277285 q = 1) (hb : d277558 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d277285, d277558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d277285, d277558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro69563 (p : Pattern) (ha : d277291 p = 1) (hb : d277564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d277286 q = 1) (hb : d277559 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d277286, d277559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277286, d277559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69562 q ha hb
  have h2 (q : Pattern) (ha : d277287 q = 1) (hb : d277560 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d277287, d277560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277287, d277560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d277288 q = 1) (hb : d277561 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d277288, d277561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277288, d277561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d277289 q = 1) (hb : d277562 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d277289, d277562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277289, d277562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d277290 q = 1) (hb : d277563 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d277290, d277563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277290, d277563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d277291 q = 1) (hb : d277564 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d277291, d277564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277291, d277564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69564 (p : Pattern) (ha : d276171 p = 1) (hb : d277571 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d272072 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d272081 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d272125 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d276166 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d276167 q = 1) (hb : d277567 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d276167, d277567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d276167, d277567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d272200 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d276168 q = 1) (hb : d277568 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d276168, d277568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d276168, d277568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d276169 q = 1) (hb : d277569 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d276169, d277569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d276169, d277569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d276170 q = 1) (hb : d277570 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d276170, d277570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d276170, d277570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d276171 q = 1) (hb : d277571 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d276171, d277571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d276171, d277571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro69565 (p : Pattern) (ha : d276181 p = 1) (hb : d277576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272072 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d272081 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d272125 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d276166 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d276167 q = 1) (hb : d277567 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d276167, d277567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d276167, d277567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d272200 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d276168 q = 1) (hb : d277568 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d276168, d277568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d276168, d277568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d276169 q = 1) (hb : d277569 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d276169, d277569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d276169, d277569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d276170 q = 1) (hb : d277570 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d276170, d277570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d276170, d277570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d272210 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d272215 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d272217 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d276176 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d276177 q = 1) (hb : d277572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d276177, d277572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d276177, d277572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d272224 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d276178 q = 1) (hb : d277573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d276178, d277573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d276178, d277573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d276179 q = 1) (hb : d277574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d276179, d277574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d276179, d277574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d276180 q = 1) (hb : d277575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d276180, d277575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d276180, d277575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d276181 q = 1) (hb : d277576 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d276181, d277576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d276181, d277576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro69566 (p : Pattern) (ha : d277296 p = 1) (hb : d277583 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d272217 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d276176 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d276177 q = 1) (hb : d277572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d276177, d277572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d276177, d277572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d272224 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d276178 q = 1) (hb : d277573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d276178, d277573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d276178, d277573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d276179 q = 1) (hb : d277581 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d276179, d277581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d276179, d277581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d276180 q = 1) (hb : d277582 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d276180, d277582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d276180, d277582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d277296 q = 1) (hb : d277583 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d277296, d277583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277296, d277583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69567 (p : Pattern) (ha : d277311 p = 1) (hb : d277593 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d272317 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d277306 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d277307 q = 1) (hb : d277589 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d277307, d277589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277307, d277589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d272372 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d277308 q = 1) (hb : d277590 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d277308, d277590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d277308, d277590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d277309 q = 1) (hb : d277591 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d277309, d277591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277309, d277591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d277310 q = 1) (hb : d277592 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d277310, d277592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277310, d277592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d277311 q = 1) (hb : d277593 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d277311, d277593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277311, d277593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69568 (p : Pattern) (ha : d277317 p = 1) (hb : d277599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272064 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d276182 q = 1) (hb : d277577 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d276182, d277577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69564 q ha hb
    | true =>
      simp only [d276182, d277577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69565 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d272242 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d276183 q = 1) (hb : d277578 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d276183, d277578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d276183, d277578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d277294 q = 1) (hb : d277579 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d277294, d277579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d277294, d277579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d277295 q = 1) (hb : d277580 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d277295, d277580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277295, d277580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d277297 q = 1) (hb : d277584 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d277297, d277584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d277297, d277584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69566 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d272251 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d277298 q = 1) (hb : d277585 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d277298, d277585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d277298, d277585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d277299 q = 1) (hb : d277586 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d277299, d277586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d277299, d277586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d277300 q = 1) (hb : d277587 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d277300, d277587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d277300, d277587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d277301 q = 1) (hb : d277588 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d277301, d277588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d277301, d277588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d277312 q = 1) (hb : d277594 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d277312, d277594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d277312, d277594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69567 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d272388 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d277313 q = 1) (hb : d277595 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d277313, d277595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d277313, d277595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d277314 q = 1) (hb : d277596 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d277314, d277596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d277314, d277596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d277315 q = 1) (hb : d277597 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d277315, d277597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d277315, d277597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d277316 q = 1) (hb : d277598 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d277316, d277598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d277316, d277598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d277317 q = 1) (hb : d277599 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d277317, d277599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d277317, d277599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro69569 (p : Pattern) (ha : d277323 p = 1) (hb : d277605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d277318 q = 1) (hb : d277600 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d277318, d277600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277318, d277600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69568 q ha hb
  have h2 (q : Pattern) (ha : d277319 q = 1) (hb : d277601 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d277319, d277601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277319, d277601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d277320 q = 1) (hb : d277602 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d277320, d277602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277320, d277602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d277321 q = 1) (hb : d277603 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d277321, d277603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277321, d277603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d277322 q = 1) (hb : d277604 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d277322, d277604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277322, d277604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d277323 q = 1) (hb : d277605 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d277323, d277605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277323, d277605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69570 (p : Pattern) (ha : d276535 p = 1) (hb : d277613 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d272552 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d272561 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d272611 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d276530 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d276531 q = 1) (hb : d277609 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d276531, d277609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d276531, d277609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d272751 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d276532 q = 1) (hb : d277610 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d276532, d277610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d276532, d277610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d276533 q = 1) (hb : d277611 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d276533, d277611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d276533, d277611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d276534 q = 1) (hb : d277612 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d276534, d277612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d276534, d277612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d276535 q = 1) (hb : d277613 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d276535, d277613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d276535, d277613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro69571 (p : Pattern) (ha : d276545 p = 1) (hb : d277618 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272552 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d272561 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d272611 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d276530 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d276531 q = 1) (hb : d277609 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d276531, d277609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d276531, d277609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d272751 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d276532 q = 1) (hb : d277610 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d276532, d277610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d276532, d277610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d276533 q = 1) (hb : d277611 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d276533, d277611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d276533, d277611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d276534 q = 1) (hb : d277612 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d276534, d277612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d276534, d277612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d272761 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d272766 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d272769 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d276540 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d276541 q = 1) (hb : d277614 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d276541, d277614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d276541, d277614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d272776 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d276542 q = 1) (hb : d277615 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d276542, d277615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d276542, d277615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d276543 q = 1) (hb : d277616 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d276543, d277616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d276543, d277616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d276544 q = 1) (hb : d277617 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d276544, d277617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d276544, d277617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d276545 q = 1) (hb : d277618 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d276545, d277618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d276545, d277618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro69572 (p : Pattern) (ha : d277329 p = 1) (hb : d277625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d272769 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d276540 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d276541 q = 1) (hb : d277614 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d276541, d277614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d276541, d277614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d272776 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d276542 q = 1) (hb : d277615 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d276542, d277615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d276542, d277615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d276543 q = 1) (hb : d277623 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d276543, d277623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d276543, d277623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d276544 q = 1) (hb : d277624 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d276544, d277624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d276544, d277624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d277329 q = 1) (hb : d277625 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d277329, d277625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277329, d277625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69573 (p : Pattern) (ha : d277348 p = 1) (hb : d277635 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d272912 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d277343 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d277344 q = 1) (hb : d277631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d277344, d277631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277344, d277631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d272999 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d277345 q = 1) (hb : d277632 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d277345, d277632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d277345, d277632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d277346 q = 1) (hb : d277633 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d277346, d277633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277346, d277633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d277347 q = 1) (hb : d277634 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d277347, d277634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277347, d277634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d277348 q = 1) (hb : d277635 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d277348, d277635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277348, d277635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69574 (p : Pattern) (ha : d277354 p = 1) (hb : d277641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d272544 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d276546 q = 1) (hb : d277619 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d276546, d277619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69570 q ha hb
    | true =>
      simp only [d276546, d277619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69571 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d272799 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d276547 q = 1) (hb : d277620 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d276547, d277620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d276547, d277620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d277327 q = 1) (hb : d277621 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d277327, d277621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d277327, d277621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d277328 q = 1) (hb : d277622 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d277328, d277622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277328, d277622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d277330 q = 1) (hb : d277626 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d277330, d277626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d277330, d277626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69572 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d272808 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d277331 q = 1) (hb : d277627 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d277331, d277627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d277331, d277627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d277332 q = 1) (hb : d277628 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d277332, d277628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d277332, d277628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d277333 q = 1) (hb : d277629 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d277333, d277629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d277333, d277629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d277334 q = 1) (hb : d277630 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d277334, d277630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d277334, d277630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d277349 q = 1) (hb : d277636 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d277349, d277636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d277349, d277636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69573 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d273015 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d277350 q = 1) (hb : d277637 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d277350, d277637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d277350, d277637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d277351 q = 1) (hb : d277638 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d277351, d277638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d277351, d277638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d277352 q = 1) (hb : d277639 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d277352, d277639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d277352, d277639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d277353 q = 1) (hb : d277640 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d277353, d277640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d277353, d277640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d277354 q = 1) (hb : d277641 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d277354, d277641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d277354, d277641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro69575 (p : Pattern) (ha : d277360 p = 1) (hb : d277647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d277355 q = 1) (hb : d277642 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d277355, d277642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277355, d277642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69574 q ha hb
  have h2 (q : Pattern) (ha : d277356 q = 1) (hb : d277643 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d277356, d277643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277356, d277643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d277357 q = 1) (hb : d277644 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d277357, d277644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277357, d277644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d277358 q = 1) (hb : d277645 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d277358, d277645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277358, d277645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d277359 q = 1) (hb : d277646 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d277359, d277646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277359, d277646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d277360 q = 1) (hb : d277647 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d277360, d277647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277360, d277647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69576 (p : Pattern) (ha : d276922 p = 1) (hb : d277656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d273180 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d273189 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d273217 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d276917 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d276918 q = 1) (hb : d277652 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d276918, d277652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d276918, d277652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d273374 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d276919 q = 1) (hb : d277653 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d276919, d277653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d276919, d277653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d276920 q = 1) (hb : d277654 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d276920, d277654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d276920, d277654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d276921 q = 1) (hb : d277655 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d276921, d277655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d276921, d277655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d276922 q = 1) (hb : d277656 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d276922, d277656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d276922, d277656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro69577 (p : Pattern) (ha : d276932 p = 1) (hb : d277661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d273180 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d273189 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d273217 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d276917 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d276918 q = 1) (hb : d277652 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d276918, d277652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d276918, d277652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d273374 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d276919 q = 1) (hb : d277653 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d276919, d277653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d276919, d277653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d276920 q = 1) (hb : d277654 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d276920, d277654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d276920, d277654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d276921 q = 1) (hb : d277655 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d276921, d277655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d276921, d277655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d273384 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d273389 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d273392 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d276927 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d276928 q = 1) (hb : d277657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d276928, d277657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d276928, d277657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d273399 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d276929 q = 1) (hb : d277658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d276929, d277658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d276929, d277658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d276930 q = 1) (hb : d277659 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d276930, d277659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d276930, d277659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d276931 q = 1) (hb : d277660 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d276931, d277660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d276931, d277660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d276932 q = 1) (hb : d277661 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d276932, d277661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d276932, d277661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro69578 (p : Pattern) (ha : d277367 p = 1) (hb : d277668 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d273392 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d276927 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d276928 q = 1) (hb : d277657 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d276928, d277657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d276928, d277657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d273399 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d276929 q = 1) (hb : d277658 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d276929, d277658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d276929, d277658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d276930 q = 1) (hb : d277666 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d276930, d277666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d276930, d277666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d276931 q = 1) (hb : d277667 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d276931, d277667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d276931, d277667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d277367 q = 1) (hb : d277668 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d277367, d277668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277367, d277668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69579 (p : Pattern) (ha : d277386 p = 1) (hb : d277678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d273521 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d277381 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d277382 q = 1) (hb : d277674 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d277382, d277674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277382, d277674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d273619 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d277383 q = 1) (hb : d277675 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d277383, d277675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d277383, d277675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d277384 q = 1) (hb : d277676 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d277384, d277676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277384, d277676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d277385 q = 1) (hb : d277677 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d277385, d277677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277385, d277677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d277386 q = 1) (hb : d277678 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d277386, d277678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277386, d277678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69580 (p : Pattern) (ha : d277392 p = 1) (hb : d277684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d273172 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d276933 q = 1) (hb : d277662 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d276933, d277662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69576 q ha hb
    | true =>
      simp only [d276933, d277662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69577 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d273422 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d276934 q = 1) (hb : d277663 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d276934, d277663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d276934, d277663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d277365 q = 1) (hb : d277664 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d277365, d277664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d277365, d277664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d277366 q = 1) (hb : d277665 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d277366, d277665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277366, d277665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d277368 q = 1) (hb : d277669 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d277368, d277669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d277368, d277669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69578 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d273431 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d277369 q = 1) (hb : d277670 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d277369, d277670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d277369, d277670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d277370 q = 1) (hb : d277671 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d277370, d277671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d277370, d277671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d277371 q = 1) (hb : d277672 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d277371, d277672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d277371, d277672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d277372 q = 1) (hb : d277673 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d277372, d277673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d277372, d277673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d277387 q = 1) (hb : d277679 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d277387, d277679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d277387, d277679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69579 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d273635 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d277388 q = 1) (hb : d277680 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d277388, d277680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d277388, d277680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d277389 q = 1) (hb : d277681 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d277389, d277681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d277389, d277681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d277390 q = 1) (hb : d277682 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d277390, d277682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d277390, d277682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d277391 q = 1) (hb : d277683 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d277391, d277683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d277391, d277683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d277392 q = 1) (hb : d277684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d277392, d277684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d277392, d277684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro69581 (p : Pattern) (ha : d277398 p = 1) (hb : d277690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d277393 q = 1) (hb : d277685 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d277393, d277685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277393, d277685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69580 q ha hb
  have h2 (q : Pattern) (ha : d277394 q = 1) (hb : d277686 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d277394, d277686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277394, d277686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d277395 q = 1) (hb : d277687 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d277395, d277687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277395, d277687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d277396 q = 1) (hb : d277688 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d277396, d277688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277396, d277688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d277397 q = 1) (hb : d277689 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d277397, d277689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277397, d277689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d277398 q = 1) (hb : d277690 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d277398, d277690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277398, d277690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69582 (p : Pattern) (ha : d277404 p = 1) (hb : d277696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d277265 q = 1) (hb : d277525 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d277265, d277525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69551 q ha hb
    | true =>
      simp only [d277265, d277525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69557 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d277292 q = 1) (hb : d277565 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d277292, d277565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277292, d277565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69563 q ha hb
  have h3 (q : Pattern) (ha : d277293 q = 1) (hb : d277566 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d277293, d277566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d277293, d277566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d277324 q = 1) (hb : d277606 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d277324, d277606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277324, d277606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69569 q ha hb
  have h5 (q : Pattern) (ha : d277325 q = 1) (hb : d277607 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d277325, d277607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277325, d277607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d277326 q = 1) (hb : d277608 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d277326, d277608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d277326, d277608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d277361 q = 1) (hb : d277648 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d277361, d277648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277361, d277648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69575 q ha hb
  have h8 (q : Pattern) (ha : d277362 q = 1) (hb : d277649 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d277362, d277649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277362, d277649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d277363 q = 1) (hb : d277650 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d277363, d277650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277363, d277650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d277364 q = 1) (hb : d277651 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d277364, d277651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d277364, d277651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d277399 q = 1) (hb : d277691 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d277399, d277691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277399, d277691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69581 q ha hb
  have h12 (q : Pattern) (ha : d277400 q = 1) (hb : d277692 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d277400, d277692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277400, d277692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d277401 q = 1) (hb : d277693 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d277401, d277693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277401, d277693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d277402 q = 1) (hb : d277694 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d277402, d277694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277402, d277694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d277403 q = 1) (hb : d277695 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d277403, d277695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d277403, d277695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d277404 q = 1) (hb : d277696 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d277404, d277696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d277404, d277696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro69583 (p : Pattern) (ha : d277410 p = 1) (hb : d277702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d277405 q = 1) (hb : d277697 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d277405, d277697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69582 q ha hb
    | true =>
      simp only [d277405, d277697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d277406 q = 1) (hb : d277698 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d277406, d277698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277406, d277698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d277407 q = 1) (hb : d277699 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d277407, d277699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d277407, d277699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d277408 q = 1) (hb : d277700 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d277408, d277700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d277408, d277700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d277409 q = 1) (hb : d277701 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d277409, d277701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d277409, d277701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d277410 q = 1) (hb : d277702 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d277410, d277702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d277410, d277702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69584 (p : Pattern) (ha : d277416 p = 1) (hb : d277708 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d277411 q = 1) (hb : d277703 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d277411, d277703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69583 q ha hb
    | true =>
      simp only [d277411, d277703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d277412 q = 1) (hb : d277704 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d277412, d277704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277412, d277704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d277413 q = 1) (hb : d277705 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d277413, d277705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d277413, d277705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d277414 q = 1) (hb : d277706 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d277414, d277706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d277414, d277706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d277415 q = 1) (hb : d277707 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d277415, d277707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d277415, d277707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d277416 q = 1) (hb : d277708 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d277416, d277708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d277416, d277708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69585 (p : Pattern) (ha : d277422 p = 1) (hb : d277714 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d277417 q = 1) (hb : d277709 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d277417, d277709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69584 q ha hb
    | true =>
      simp only [d277417, d277709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d277418 q = 1) (hb : d277710 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d277418, d277710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277418, d277710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d277419 q = 1) (hb : d277711 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d277419, d277711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d277419, d277711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d277420 q = 1) (hb : d277712 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d277420, d277712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d277420, d277712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d277421 q = 1) (hb : d277713 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d277421, d277713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d277421, d277713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d277422 q = 1) (hb : d277714 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d277422, d277714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d277422, d277714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69586 (p : Pattern) (ha : d277428 p = 1) (hb : d277720 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d277423 q = 1) (hb : d277715 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d277423, d277715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69585 q ha hb
    | true =>
      simp only [d277423, d277715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d277424 q = 1) (hb : d277716 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d277424, d277716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277424, d277716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d277425 q = 1) (hb : d277717 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d277425, d277717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d277425, d277717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d277426 q = 1) (hb : d277718 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d277426, d277718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d277426, d277718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d277427 q = 1) (hb : d277719 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d277427, d277719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d277427, d277719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d277428 q = 1) (hb : d277720 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d277428, d277720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d277428, d277720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69587 (p : Pattern) (ha : d277434 p = 1) (hb : d277726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d277429 q = 1) (hb : d277721 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d277429, d277721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69586 q ha hb
    | true =>
      simp only [d277429, d277721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d277430 q = 1) (hb : d277722 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d277430, d277722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277430, d277722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d277431 q = 1) (hb : d277723 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d277431, d277723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d277431, d277723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d277432 q = 1) (hb : d277724 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d277432, d277724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d277432, d277724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d277433 q = 1) (hb : d277725 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d277433, d277725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d277433, d277725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d277434 q = 1) (hb : d277726 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d277434, d277726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d277434, d277726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69588 (p : Pattern) (ha : d277440 p = 1) (hb : d277732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d277435 q = 1) (hb : d277727 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d277435, d277727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69587 q ha hb
    | true =>
      simp only [d277435, d277727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d277436 q = 1) (hb : d277728 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d277436, d277728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277436, d277728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d277437 q = 1) (hb : d277729 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d277437, d277729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d277437, d277729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d277438 q = 1) (hb : d277730 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d277438, d277730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d277438, d277730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d277439 q = 1) (hb : d277731 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d277439, d277731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d277439, d277731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d277440 q = 1) (hb : d277732 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d277440, d277732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d277440, d277732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69589 (p : Pattern) (ha : d277446 p = 1) (hb : d277738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d277441 q = 1) (hb : d277733 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d277441, d277733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69588 q ha hb
    | true =>
      simp only [d277441, d277733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d277442 q = 1) (hb : d277734 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d277442, d277734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d277442, d277734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d277443 q = 1) (hb : d277735 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d277443, d277735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d277443, d277735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d277444 q = 1) (hb : d277736 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d277444, d277736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d277444, d277736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d277445 q = 1) (hb : d277737 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d277445, d277737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d277445, d277737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d277446 q = 1) (hb : d277738 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d277446, d277738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d277446, d277738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69590 (p : Pattern) (ha : d211416 p = 1) (hb : d212438 p = 1) : d212438 p = 1 := by
  have h0 (q : Pattern) (ha : d211416 q = 1) (hb : d212438 q = 1) : d212438 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro69591 (p : Pattern) (ha : d211416 p = 1) (hb : d212558 p = 1) : d212558 p = 1 := by
  have h0 (q : Pattern) (ha : d211416 q = 1) (hb : d212558 q = 1) : d212558 q = 1 := by
    exact hb
  exact h0 p ha hb
theorem andIntro69592 (p : Pattern) (ha : d132 p = 1) (hb : d277739 p = 1) : d277741 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d129 q = 1) : d129 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d15 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130 q = 1) (hb : d216468 q = 1) : d534 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d216468, d534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130, d216468, d534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d16 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d131 q = 1) (hb : d277739 q = 1) : d33559 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d131, d277739, d33559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131, d277739, d33559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d17 q = 1) (hb : d277739 q = 1) : d17 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d132 q = 1) (hb : d277739 q = 1) : d277741 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d132, d277741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132, d277741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69593 (p : Pattern) (ha : d138 p = 1) (hb : d277740 p = 1) : d277747 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69592 q ha hb
    | true =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d134 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d277740 q = 1) : d20 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d277740 q = 1) : d277744 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d135, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d277740 q = 1) : d21 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d136 q = 1) (hb : d277740 q = 1) : d277745 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d277745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136, d277745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d137 q = 1) (hb : d277740 q = 1) : d277746 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d277746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137, d277746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d23 q = 1) (hb : d277740 q = 1) : d23 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d138 q = 1) (hb : d277740 q = 1) : d277747 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d138, d277747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d138, d277747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro69594 (p : Pattern) (ha : d144 p = 1) (hb : d277740 p = 1) : d277753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d139 q = 1) (hb : d277740 q = 1) : d277748 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d277748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69593 q ha hb
    | true =>
      simp only [d139, d277748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d140 q = 1) (hb : d277740 q = 1) : d277749 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d277749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d140, d277749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d141 q = 1) (hb : d277740 q = 1) : d277750 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d277750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d277750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d142 q = 1) (hb : d277740 q = 1) : d277751 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d277751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d142, d277751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d277740 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d143 q = 1) (hb : d277740 q = 1) : d277752 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d143, d277752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d143, d277752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d277740 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d144 q = 1) (hb : d277740 q = 1) : d277753 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d144, d277753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d144, d277753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69595 (p : Pattern) (ha : d150 p = 1) (hb : d277740 p = 1) : d277759 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d277740 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d277740 q = 1) : d277754 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d277754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69594 q ha hb
    | true =>
      simp only [d145, d277754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d277740 q = 1) : d277755 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d277755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d277755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d277740 q = 1) : d277756 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d277756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d277756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d277740 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148 q = 1) (hb : d277740 q = 1) : d277757 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d277757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148, d277757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d277740 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d149 q = 1) (hb : d277740 q = 1) : d277758 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d277758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d149, d277758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150 q = 1) (hb : d277740 q = 1) : d277759 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d150, d277759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d150, d277759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro69596 (p : Pattern) (ha : d203 p = 1) (hb : d277740 p = 1) : d277772 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d277740 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69595 q ha hb
    | true =>
      simp only [d151, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d277740 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d277740 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d277740 q = 1) : d277762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d277740 q = 1) : d277763 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d277763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d277763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d277740 q = 1) : d277764 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d277764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d277764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d203 q = 1) (hb : d277740 q = 1) : d277772 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d203, d277772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d203, d277772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro69597 (p : Pattern) (ha : d4349 p = 1) (hb : d277740 p = 1) : d277785 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d277740 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d204 q = 1) (hb : d277740 q = 1) : d277773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69596 q ha hb
    | true =>
      simp only [d204, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4340 q = 1) (hb : d277740 q = 1) : d277774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d277774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4340, d277774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d277740 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4341 q = 1) (hb : d277740 q = 1) : d277775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d277775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4341, d277775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4342 q = 1) (hb : d277740 q = 1) : d277783 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4342, d277783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4342, d277783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4343 q = 1) (hb : d277740 q = 1) : d277784 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4343, d277784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4343, d277784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4349 q = 1) (hb : d277740 q = 1) : d277785 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4349, d277785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4349, d277785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69598 (p : Pattern) (ha : d231 p = 1) (hb : d277740 p = 1) : d277796 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d226 q = 1) (hb : d277740 q = 1) : d277791 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d277791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d277791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69593 q ha hb
  have h2 (q : Pattern) (ha : d139 q = 1) (hb : d277740 q = 1) : d277748 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d277748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69593 q ha hb
    | true =>
      simp only [d139, d277748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d227 q = 1) (hb : d277740 q = 1) : d277792 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d277792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d227, d277792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d140 q = 1) (hb : d277740 q = 1) : d277749 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d277749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d140, d277749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d228 q = 1) (hb : d277740 q = 1) : d277793 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d277793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d228, d277793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d229 q = 1) (hb : d277740 q = 1) : d277794 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d277794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d229, d277794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d277740 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d230 q = 1) (hb : d277740 q = 1) : d277795 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d230, d277795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d230, d277795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d277740 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d231 q = 1) (hb : d277740 q = 1) : d277796 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d231, d277796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d231, d277796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro69599 (p : Pattern) (ha : d237 p = 1) (hb : d277740 p = 1) : d277802 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d277740 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d277740 q = 1) : d277797 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d277797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69598 q ha hb
    | true =>
      simp only [d232, d277797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d277740 q = 1) : d277798 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d277798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d277798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d277740 q = 1) : d277799 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d277799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d277799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d277740 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d235 q = 1) (hb : d277740 q = 1) : d277800 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d277800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d235, d277800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d277740 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d236 q = 1) (hb : d277740 q = 1) : d277801 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d236, d277801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d236, d277801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d237 q = 1) (hb : d277740 q = 1) : d277802 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d237, d277802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d237, d277802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro69600 (p : Pattern) (ha : d243 p = 1) (hb : d277740 p = 1) : d277808 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d277740 q = 1) : d277803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d277803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69599 q ha hb
    | true =>
      simp only [d238, d277803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d277740 q = 1) : d277804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d277804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d277804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d277740 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d240 q = 1) (hb : d277740 q = 1) : d277805 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d240, d277805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d240, d277805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241 q = 1) (hb : d277740 q = 1) : d277806 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d241, d277806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d241, d277806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d242 q = 1) (hb : d277740 q = 1) : d277807 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d242, d277807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d242, d277807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d243 q = 1) (hb : d277740 q = 1) : d277808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d243, d277808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d243, d277808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro69601 (p : Pattern) (ha : d4359 p = 1) (hb : d277740 p = 1) : d277814 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d277740 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d244 q = 1) (hb : d277740 q = 1) : d277809 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d244, d277809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69600 q ha hb
    | true =>
      simp only [d244, d277809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4355 q = 1) (hb : d277740 q = 1) : d277810 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4355, d277810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4355, d277810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d277740 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4356 q = 1) (hb : d277740 q = 1) : d277811 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4356, d277811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4356, d277811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d4357 q = 1) (hb : d277740 q = 1) : d277812 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d4357, d277812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4357, d277812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4358 q = 1) (hb : d277740 q = 1) : d277813 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d4358, d277813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4358, d277813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d4359 q = 1) (hb : d277740 q = 1) : d277814 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d4359, d277814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4359, d277814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69602 (p : Pattern) (ha : d156 p = 1) (hb : d277740 p = 1) : d277765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d277740 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69595 q ha hb
    | true =>
      simp only [d151, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d277740 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d277740 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d277740 q = 1) : d277762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d277740 q = 1) : d277763 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d277763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d277763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d155 q = 1) (hb : d277740 q = 1) : d277764 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155, d277764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155, d277764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d156 q = 1) (hb : d277740 q = 1) : d277765 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156, d277765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d156, d277765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro69603 (p : Pattern) (ha : d51643 p = 1) (hb : d277740 p = 1) : d277771 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d277740 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d277740 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d277740 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d157 q = 1) (hb : d277740 q = 1) : d277766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69602 q ha hb
    | true =>
      simp only [d157, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d277740 q = 1) : d277767 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d277767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4335, d277767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d277740 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d277740 q = 1) : d277768 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d277768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d277768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d277740 q = 1) : d277769 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d277769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d51641, d277769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d277740 q = 1) : d277770 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d277770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51642, d277770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d51643 q = 1) (hb : d277740 q = 1) : d277771 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51643, d277771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51643, d277771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro69604 (p : Pattern) (ha : d51646 p = 1) (hb : d277740 p = 1) : d277778 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d277740 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d277740 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d277740 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d157 q = 1) (hb : d277740 q = 1) : d277766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69602 q ha hb
    | true =>
      simp only [d157, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d4335 q = 1) (hb : d277740 q = 1) : d277767 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4335, d277767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4335, d277767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d277740 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d4336 q = 1) (hb : d277740 q = 1) : d277768 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4336, d277768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d4336, d277768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d51641 q = 1) (hb : d277740 q = 1) : d277769 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51641, d277769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51641, d277769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d51642 q = 1) (hb : d277740 q = 1) : d277770 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51642, d277770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51642, d277770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d277740 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d277740 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d277740 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d204 q = 1) (hb : d277740 q = 1) : d277773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69596 q ha hb
    | true =>
      simp only [d204, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d4340 q = 1) (hb : d277740 q = 1) : d277774 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4340, d277774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4340, d277774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d277740 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d4341 q = 1) (hb : d277740 q = 1) : d277775 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d4341, d277775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4341, d277775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d51644 q = 1) (hb : d277740 q = 1) : d277776 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d51644, d277776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51644, d277776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d51645 q = 1) (hb : d277740 q = 1) : d277777 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d51645, d277777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d51645, d277777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d51646 q = 1) (hb : d277740 q = 1) : d277778 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d51646, d277778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d51646, d277778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro69605 (p : Pattern) (ha : d51652 p = 1) (hb : d277740 p = 1) : d277820 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d277740 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d51647 q = 1) (hb : d277740 q = 1) : d277779 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d51647, d277779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69603 q ha hb
    | true =>
      simp only [d51647, d277779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69604 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d277740 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d51648 q = 1) (hb : d277740 q = 1) : d277780 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d51648, d277780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51648, d277780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d51649 q = 1) (hb : d277740 q = 1) : d277781 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d51649, d277781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d51649, d277781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51650 q = 1) (hb : d277740 q = 1) : d277782 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d51650, d277782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51650, d277782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d4350 q = 1) (hb : d277740 q = 1) : d277786 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4350, d277786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4350, d277786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69597 q ha hb
  have h8 (q : Pattern) (ha : d4351 q = 1) (hb : d277740 q = 1) : d277787 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4351, d277787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d4351, d277787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d4352 q = 1) (hb : d277740 q = 1) : d277788 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4352, d277788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4352, d277788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d4353 q = 1) (hb : d277740 q = 1) : d277789 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4353, d277789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d4353, d277789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d51651 q = 1) (hb : d277740 q = 1) : d277790 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d51651, d277790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d51651, d277790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d4360 q = 1) (hb : d277740 q = 1) : d277815 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d4360, d277815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4360, d277815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69601 q ha hb
  have h13 (q : Pattern) (ha : d4361 q = 1) (hb : d277740 q = 1) : d277816 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d4361, d277816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d4361, d277816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d4362 q = 1) (hb : d277740 q = 1) : d277817 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d4362, d277817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d4362, d277817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d4363 q = 1) (hb : d277740 q = 1) : d277818 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d4363, d277818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d4363, d277818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d4364 q = 1) (hb : d277740 q = 1) : d277819 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d4364, d277819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d4364, d277819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d51652 q = 1) (hb : d277740 q = 1) : d277820 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d51652, d277820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d51652, d277820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro69606 (p : Pattern) (ha : d284 p = 1) (hb : d277740 p = 1) : d277830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d277740 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d277740 q = 1) : d277766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69602 q ha hb
    | true =>
      simp only [d157, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d277740 q = 1) : d277826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d277826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d277826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d277740 q = 1) : d277827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d277827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d277827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d277740 q = 1) : d277828 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d277828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d277828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d277740 q = 1) : d277829 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d277829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d277829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d284 q = 1) (hb : d277740 q = 1) : d277830 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d284, d277830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d284, d277830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro69607 (p : Pattern) (ha : d291 p = 1) (hb : d277740 p = 1) : d277837 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d277740 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d277740 q = 1) : d277766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69602 q ha hb
    | true =>
      simp only [d157, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d277740 q = 1) : d277826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d277826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d277826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d277740 q = 1) : d277827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d277827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d277827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d277740 q = 1) : d277828 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d277828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d277828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d277740 q = 1) : d277829 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d277829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d277829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d277740 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d204 q = 1) (hb : d277740 q = 1) : d277773 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d204, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69596 q ha hb
    | true =>
      simp only [d204, d277773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d287 q = 1) (hb : d277740 q = 1) : d277833 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d287, d277833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d287, d277833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d288 q = 1) (hb : d277740 q = 1) : d277834 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d288, d277834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d288, d277834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d289 q = 1) (hb : d277740 q = 1) : d277835 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d289, d277835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d289, d277835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d290 q = 1) (hb : d277740 q = 1) : d277836 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d290, d277836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d290, d277836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d291 q = 1) (hb : d277740 q = 1) : d277837 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d291, d277837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d291, d277837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro69608 (p : Pattern) (ha : d397 p = 1) (hb : d277740 p = 1) : d277918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d277740 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d157 q = 1) (hb : d277740 q = 1) : d277766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d157, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69602 q ha hb
    | true =>
      simp only [d157, d277766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d280 q = 1) (hb : d277740 q = 1) : d277826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d280, d277826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d280, d277826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d281 q = 1) (hb : d277740 q = 1) : d277827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d281, d277827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d281, d277827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d282 q = 1) (hb : d277740 q = 1) : d277828 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d282, d277828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d282, d277828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d283 q = 1) (hb : d277740 q = 1) : d277829 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d283, d277829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d283, d277829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d277740 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d397 q = 1) (hb : d277740 q = 1) : d277918 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d397, d277918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d397, d277918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69609 (p : Pattern) (ha : d296 p = 1) (hb : d277740 p = 1) : d277842 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d277740 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69595 q ha hb
    | true =>
      simp only [d151, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d277740 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d277740 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d277740 q = 1) : d277762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d277740 q = 1) : d277763 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d277763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d277763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d277740 q = 1) : d277841 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d277841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d277841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d296 q = 1) (hb : d277740 q = 1) : d277842 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d296, d277842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d296, d277842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro69610 (p : Pattern) (ha : d303 p = 1) (hb : d277740 p = 1) : d277849 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d277740 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69595 q ha hb
    | true =>
      simp only [d151, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d277740 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d277740 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d277740 q = 1) : d277762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d277740 q = 1) : d277847 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d277847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d277847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d277740 q = 1) : d277848 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d277848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d277848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d303 q = 1) (hb : d277740 q = 1) : d277849 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d303, d277849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d303, d277849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro69611 (p : Pattern) (ha : d4736 p = 1) (hb : d277740 p = 1) : d277891 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d277740 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69595 q ha hb
    | true =>
      simp only [d151, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d277740 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d277740 q = 1) : d277888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d277888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d277888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d277740 q = 1) : d277889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d277889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d277889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d277740 q = 1) : d277890 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d277890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d277890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d4736 q = 1) (hb : d277740 q = 1) : d277891 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d4736, d277891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d4736, d277891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69612 (p : Pattern) (ha : d312 p = 1) (hb : d277739 p = 1) : d277853 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d309 q = 1) : d309 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d310 q = 1) (hb : d216468 q = 1) : d825 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d130 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d311 q = 1) (hb : d277739 q = 1) : d5121 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d311, d277739, d5121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d311, d277739, d5121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d129 q = 1) : d129 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d130 q = 1) (hb : d216468 q = 1) : d534 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d216468, d534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d130, d216468, d534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d16 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131 q = 1) (hb : d277739 q = 1) : d33559 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d131, d277739, d33559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131, d277739, d33559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d312 q = 1) (hb : d277739 q = 1) : d277853 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d312, d277853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d312, d277853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro69613 (p : Pattern) (ha : d318 p = 1) (hb : d277740 p = 1) : d277859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d277739 q = 1) : d277854 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69612 q ha hb
    | true =>
      simp only [d313, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d277740 q = 1) : d277855 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69592 q ha hb
    | true =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d134 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d315 q = 1) (hb : d277740 q = 1) : d277856 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d277740 q = 1) : d20 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d135 q = 1) (hb : d277740 q = 1) : d277744 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d135, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316 q = 1) (hb : d277740 q = 1) : d277857 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d277857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316, d277857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d317 q = 1) (hb : d277740 q = 1) : d277858 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d277858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d317, d277858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21 q = 1) (hb : d277740 q = 1) : d21 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d136 q = 1) (hb : d277740 q = 1) : d277745 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d277745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d136, d277745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d137 q = 1) (hb : d277740 q = 1) : d277746 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d277746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d137, d277746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h15 (q : Pattern) (ha : d318 q = 1) (hb : d277740 q = 1) : d277859 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d318, d277859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d318, d277859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro69614 (p : Pattern) (ha : d9381 p = 1) (hb : d277740 p = 1) : d277867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69592 q ha hb
    | true =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d134 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d277740 q = 1) : d20 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d277740 q = 1) : d277744 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d135, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5448 q = 1) (hb : d277740 q = 1) : d277865 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5448, d277865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5448, d277865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d5449 q = 1) (hb : d277740 q = 1) : d277866 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5449, d277866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5449, d277866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h9 (q : Pattern) (ha : d23 q = 1) (hb : d277740 q = 1) : d23 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d9381 q = 1) (hb : d277740 q = 1) : d277867 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9381, d277867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9381, d277867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro69615 (p : Pattern) (ha : d15966 p = 1) (hb : d277740 p = 1) : d277873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d277740 q = 1) : d277860 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d277860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69613 q ha hb
    | true =>
      simp only [d319, d277860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d277740 q = 1) : d277861 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d277861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d277861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d277740 q = 1) : d277862 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d277862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d277862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d277740 q = 1) : d277863 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d277863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d277863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d139 q = 1) (hb : d277740 q = 1) : d277748 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d277748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69593 q ha hb
    | true =>
      simp only [d139, d277748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d140 q = 1) (hb : d277740 q = 1) : d277749 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d277749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d140, d277749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d141 q = 1) (hb : d277740 q = 1) : d277750 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d141, d277750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d141, d277750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d142 q = 1) (hb : d277740 q = 1) : d277751 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d142, d277751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d142, d277751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d323 q = 1) (hb : d277740 q = 1) : d277864 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d323, d277864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d323, d277864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9382 q = 1) (hb : d277740 q = 1) : d277868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d277868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69614 q ha hb
    | true =>
      simp only [d9382, d277868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9384 q = 1) (hb : d277740 q = 1) : d277869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d277869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9384, d277869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12493 q = 1) (hb : d277740 q = 1) : d277870 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d277870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d277870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12494 q = 1) (hb : d277740 q = 1) : d277871 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d277871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12494, d277871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d28 q = 1) (hb : d277740 q = 1) : d28 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d12495 q = 1) (hb : d277740 q = 1) : d277872 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d277872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12495, d277872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d15966 q = 1) (hb : d277740 q = 1) : d277873 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d15966, d277873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15966, d277873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro69616 (p : Pattern) (ha : d15972 p = 1) (hb : d277740 p = 1) : d277879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d277740 q = 1) : d277874 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d277874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69615 q ha hb
    | true =>
      simp only [d15967, d277874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69594 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d277740 q = 1) : d277875 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d277875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d277875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d277740 q = 1) : d277876 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d277876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d277876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d277740 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d277740 q = 1) : d277754 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d277754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69594 q ha hb
    | true =>
      simp only [d145, d277754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d277740 q = 1) : d277755 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d277755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d277755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d277740 q = 1) : d277756 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d277756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d277756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d277740 q = 1) : d277877 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d277877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d277877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d277740 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d148 q = 1) (hb : d277740 q = 1) : d277757 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d277757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148, d277757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15971 q = 1) (hb : d277740 q = 1) : d277878 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15971, d277878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15971, d277878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15972 q = 1) (hb : d277740 q = 1) : d277879 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d15972, d277879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15972, d277879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro69617 (p : Pattern) (ha : d15978 p = 1) (hb : d277740 p = 1) : d277885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d277740 q = 1) : d277880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d277880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69616 q ha hb
    | true =>
      simp only [d15973, d277880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d277740 q = 1) : d277881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d277881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d277881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d277740 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69595 q ha hb
    | true =>
      simp only [d151, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d277740 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d277740 q = 1) : d277882 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d277882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d277882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d277740 q = 1) : d277883 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d277883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d277883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d277740 q = 1) : d277884 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d277884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d277884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15978 q = 1) (hb : d277740 q = 1) : d277885 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15978, d277885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15978, d277885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69618 (p : Pattern) (ha : d128195 p = 1) (hb : d277740 p = 1) : d277897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d277740 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d277740 q = 1) : d277843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d277843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69609 q ha hb
    | true =>
      simp only [d297, d277843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d277740 q = 1) : d277844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d277844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d277844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d277740 q = 1) : d277845 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d277845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d277845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d277740 q = 1) : d277846 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d277846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d277846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d277740 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d277740 q = 1) : d277850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d277850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69610 q ha hb
    | true =>
      simp only [d304, d277850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d277740 q = 1) : d277851 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d277851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d277851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d277740 q = 1) : d277852 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d277852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d277852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d277740 q = 1) : d277886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d277886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69617 q ha hb
    | true =>
      simp only [d15979, d277886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69602 q ha hb
  have h11 (q : Pattern) (ha : d128191 q = 1) (hb : d277740 q = 1) : d277887 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d277887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128191, d277887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d277740 q = 1) : d277892 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d277892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69611 q ha hb
    | true =>
      simp only [d4737, d277892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d277740 q = 1) : d277893 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d277893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d277893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d128192 q = 1) (hb : d277740 q = 1) : d277894 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d277894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d277894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128193 q = 1) (hb : d277740 q = 1) : d277895 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d277895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128193, d277895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128194 q = 1) (hb : d277740 q = 1) : d277896 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d277896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128194, d277896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128195 q = 1) (hb : d277740 q = 1) : d277897 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128195, d277897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128195, d277897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro69619 (p : Pattern) (ha : d376 p = 1) (hb : d277740 p = 1) : d277898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d277740 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69595 q ha hb
    | true =>
      simp only [d151, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d277740 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d277740 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d277740 q = 1) : d277762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d154 q = 1) (hb : d277740 q = 1) : d277763 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d154, d277763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d154, d277763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d295 q = 1) (hb : d277740 q = 1) : d277841 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d295, d277841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d295, d277841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d376 q = 1) (hb : d277740 q = 1) : d277898 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d376, d277898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d376, d277898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro69620 (p : Pattern) (ha : d381 p = 1) (hb : d277740 p = 1) : d277903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d277740 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69595 q ha hb
    | true =>
      simp only [d151, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d277740 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d277740 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d153 q = 1) (hb : d277740 q = 1) : d277762 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d153, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d153, d277762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d301 q = 1) (hb : d277740 q = 1) : d277847 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d301, d277847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d301, d277847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d302 q = 1) (hb : d277740 q = 1) : d277848 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d302, d277848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d302, d277848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d381 q = 1) (hb : d277740 q = 1) : d277903 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d381, d277903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d381, d277903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro69621 (p : Pattern) (ha : d5355 p = 1) (hb : d277740 p = 1) : d277910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d151 q = 1) (hb : d277740 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69595 q ha hb
    | true =>
      simp only [d151, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d152 q = 1) (hb : d277740 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d4733 q = 1) (hb : d277740 q = 1) : d277888 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d4733, d277888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d4733, d277888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d4734 q = 1) (hb : d277740 q = 1) : d277889 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d4734, d277889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d4734, d277889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d4735 q = 1) (hb : d277740 q = 1) : d277890 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d4735, d277890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d4735, d277890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5355 q = 1) (hb : d277740 q = 1) : d277910 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5355, d277910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5355, d277910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69622 (p : Pattern) (ha : d15985 p = 1) (hb : d277740 p = 1) : d277907 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15973 q = 1) (hb : d277740 q = 1) : d277880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15973, d277880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69616 q ha hb
    | true =>
      simp only [d15973, d277880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d15974 q = 1) (hb : d277740 q = 1) : d277881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15974, d277881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15974, d277881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d151 q = 1) (hb : d277740 q = 1) : d277760 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d151, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69595 q ha hb
    | true =>
      simp only [d151, d277760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d152 q = 1) (hb : d277740 q = 1) : d277761 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d152, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d152, d277761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15975 q = 1) (hb : d277740 q = 1) : d277882 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d15975, d277882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15975, d277882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15976 q = 1) (hb : d277740 q = 1) : d277883 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d15976, d277883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d15976, d277883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d15977 q = 1) (hb : d277740 q = 1) : d277884 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d15977, d277884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15977, d277884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15985 q = 1) (hb : d277740 q = 1) : d277907 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d15985, d277907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15985, d277907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro69623 (p : Pattern) (ha : d128200 p = 1) (hb : d277740 p = 1) : d277916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d277740 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d297 q = 1) (hb : d277740 q = 1) : d277843 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d297, d277843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69609 q ha hb
    | true =>
      simp only [d297, d277843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d298 q = 1) (hb : d277740 q = 1) : d277844 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d298, d277844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d298, d277844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d299 q = 1) (hb : d277740 q = 1) : d277845 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d299, d277845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d299, d277845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d300 q = 1) (hb : d277740 q = 1) : d277846 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d300, d277846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d300, d277846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d277740 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d304 q = 1) (hb : d277740 q = 1) : d277850 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d304, d277850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69610 q ha hb
    | true =>
      simp only [d304, d277850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d305 q = 1) (hb : d277740 q = 1) : d277851 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d305, d277851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d305, d277851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d306 q = 1) (hb : d277740 q = 1) : d277852 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d306, d277852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d306, d277852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15979 q = 1) (hb : d277740 q = 1) : d277886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15979, d277886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69617 q ha hb
    | true =>
      simp only [d15979, d277886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69602 q ha hb
  have h11 (q : Pattern) (ha : d128191 q = 1) (hb : d277740 q = 1) : d277887 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128191, d277887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128191, d277887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d4737 q = 1) (hb : d277740 q = 1) : d277892 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d4737, d277892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69611 q ha hb
    | true =>
      simp only [d4737, d277892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d5350 q = 1) (hb : d277740 q = 1) : d277893 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5350, d277893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d5350, d277893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d128192 q = 1) (hb : d277740 q = 1) : d277894 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128192, d277894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128192, d277894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128193 q = 1) (hb : d277740 q = 1) : d277895 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128193, d277895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128193, d277895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d128194 q = 1) (hb : d277740 q = 1) : d277896 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128194, d277896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128194, d277896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d277740 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d377 q = 1) (hb : d277740 q = 1) : d277899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d377, d277899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69619 q ha hb
    | true =>
      simp only [d377, d277899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d378 q = 1) (hb : d277740 q = 1) : d277900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d378, d277900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d378, d277900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d379 q = 1) (hb : d277740 q = 1) : d277901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d379, d277901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d379, d277901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d380 q = 1) (hb : d277740 q = 1) : d277902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d380, d277902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d380, d277902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d277740 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d382 q = 1) (hb : d277740 q = 1) : d277904 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d382, d277904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69620 q ha hb
    | true =>
      simp only [d382, d277904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d383 q = 1) (hb : d277740 q = 1) : d277905 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d383, d277905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d383, d277905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d384 q = 1) (hb : d277740 q = 1) : d277906 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d384, d277906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d384, d277906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d15986 q = 1) (hb : d277740 q = 1) : d277908 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d277908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69622 q ha hb
    | true =>
      simp only [d15986, d277908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69596 q ha hb
  have h27 (q : Pattern) (ha : d128196 q = 1) (hb : d277740 q = 1) : d277909 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d277909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d128196, d277909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d5356 q = 1) (hb : d277740 q = 1) : d277911 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d277911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69621 q ha hb
    | true =>
      simp only [d5356, d277911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d5357 q = 1) (hb : d277740 q = 1) : d277912 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d277912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d5357, d277912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d128197 q = 1) (hb : d277740 q = 1) : d277913 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d277913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d128197, d277913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d128198 q = 1) (hb : d277740 q = 1) : d277914 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128198, d277914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d128198, d277914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d128199 q = 1) (hb : d277740 q = 1) : d277915 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128199, d277915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128199, d277915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d128200 q = 1) (hb : d277740 q = 1) : d277916 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128200, d277916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128200, d277916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro69624 (p : Pattern) (ha : d128207 p = 1) (hb : d277740 p = 1) : d277925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15986 q = 1) (hb : d277740 q = 1) : d277908 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15986, d277908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69622 q ha hb
    | true =>
      simp only [d15986, d277908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69596 q ha hb
  have h2 (q : Pattern) (ha : d128196 q = 1) (hb : d277740 q = 1) : d277909 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128196, d277909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128196, d277909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5356 q = 1) (hb : d277740 q = 1) : d277911 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5356, d277911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69621 q ha hb
    | true =>
      simp only [d5356, d277911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5357 q = 1) (hb : d277740 q = 1) : d277912 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5357, d277912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5357, d277912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128197 q = 1) (hb : d277740 q = 1) : d277913 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128197, d277913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128197, d277913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128205 q = 1) (hb : d277740 q = 1) : d277923 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128205, d277923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128205, d277923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128206 q = 1) (hb : d277740 q = 1) : d277924 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128206, d277924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128206, d277924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128207 q = 1) (hb : d277740 q = 1) : d277925 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128207, d277925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128207, d277925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69625 (p : Pattern) (ha : d5377 p = 1) (hb : d277740 p = 1) : d277959 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238 q = 1) (hb : d277740 q = 1) : d277803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d277803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69599 q ha hb
    | true =>
      simp only [d238, d277803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239 q = 1) (hb : d277740 q = 1) : d277804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d277804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d277804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5374 q = 1) (hb : d277740 q = 1) : d277956 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5374, d277956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5374, d277956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5375 q = 1) (hb : d277740 q = 1) : d277957 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5375, d277957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5375, d277957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5376 q = 1) (hb : d277740 q = 1) : d277958 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5376, d277958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5376, d277958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5377 q = 1) (hb : d277740 q = 1) : d277959 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5377, d277959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5377, d277959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69626 (p : Pattern) (ha : d16004 p = 1) (hb : d277740 p = 1) : d277941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d277740 q = 1) : d277931 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d277931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d277931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69613 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d277740 q = 1) : d277860 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d277860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69613 q ha hb
    | true =>
      simp only [d319, d277860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d277740 q = 1) : d277932 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d277932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d277932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d277740 q = 1) : d277861 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d277861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d277861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d277740 q = 1) : d277933 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d277933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d277933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d277740 q = 1) : d277934 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d277934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d277934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d226 q = 1) (hb : d277740 q = 1) : d277791 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d277791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d277791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69593 q ha hb
  have h8 (q : Pattern) (ha : d139 q = 1) (hb : d277740 q = 1) : d277748 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d139, d277748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69593 q ha hb
    | true =>
      simp only [d139, d277748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d227 q = 1) (hb : d277740 q = 1) : d277792 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d227, d277792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d227, d277792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d140 q = 1) (hb : d277740 q = 1) : d277749 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d140, d277749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d140, d277749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d228 q = 1) (hb : d277740 q = 1) : d277793 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d228, d277793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d228, d277793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d229 q = 1) (hb : d277740 q = 1) : d277794 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d229, d277794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d229, d277794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d416 q = 1) (hb : d277740 q = 1) : d277935 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d416, d277935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d416, d277935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12599 q = 1) (hb : d277740 q = 1) : d277936 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d277936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d277936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69614 q ha hb
  have h15 (q : Pattern) (ha : d9382 q = 1) (hb : d277740 q = 1) : d277868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d277868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69614 q ha hb
    | true =>
      simp only [d9382, d277868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12600 q = 1) (hb : d277740 q = 1) : d277937 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d277937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12600, d277937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9384 q = 1) (hb : d277740 q = 1) : d277869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d277869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9384, d277869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12601 q = 1) (hb : d277740 q = 1) : d277938 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d277938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12601, d277938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12602 q = 1) (hb : d277740 q = 1) : d277939 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d277939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12602, d277939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d69 q = 1) (hb : d277740 q = 1) : d69 q = 1 := by
    exact ha
  have h21 (q : Pattern) (ha : d12603 q = 1) (hb : d277740 q = 1) : d277940 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d277940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12603, d277940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d16004 q = 1) (hb : d277740 q = 1) : d277941 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16004, d277941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16004, d277941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro69627 (p : Pattern) (ha : d16010 p = 1) (hb : d277740 p = 1) : d277947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d277740 q = 1) : d277942 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d277942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69626 q ha hb
    | true =>
      simp only [d16005, d277942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69598 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d277740 q = 1) : d277943 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d277943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d277943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d277740 q = 1) : d277944 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d277944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d277944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d277740 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d277740 q = 1) : d277797 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d277797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69598 q ha hb
    | true =>
      simp only [d232, d277797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d277740 q = 1) : d277798 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d277798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d277798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d277740 q = 1) : d277799 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d277799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d277799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d277740 q = 1) : d277945 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d277945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d277945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d277740 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d235 q = 1) (hb : d277740 q = 1) : d277800 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d235, d277800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d235, d277800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16009 q = 1) (hb : d277740 q = 1) : d277946 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16009, d277946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16009, d277946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16010 q = 1) (hb : d277740 q = 1) : d277947 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16010, d277947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16010, d277947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro69628 (p : Pattern) (ha : d16016 p = 1) (hb : d277740 p = 1) : d277953 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16011 q = 1) (hb : d277740 q = 1) : d277948 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16011, d277948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69627 q ha hb
    | true =>
      simp only [d16011, d277948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16012 q = 1) (hb : d277740 q = 1) : d277949 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16012, d277949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16012, d277949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238 q = 1) (hb : d277740 q = 1) : d277803 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d238, d277803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69599 q ha hb
    | true =>
      simp only [d238, d277803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239 q = 1) (hb : d277740 q = 1) : d277804 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d239, d277804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239, d277804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16013 q = 1) (hb : d277740 q = 1) : d277950 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16013, d277950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16013, d277950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16014 q = 1) (hb : d277740 q = 1) : d277951 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16014, d277951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16014, d277951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16015 q = 1) (hb : d277740 q = 1) : d277952 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16015, d277952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16015, d277952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16016 q = 1) (hb : d277740 q = 1) : d277953 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16016, d277953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16016, d277953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro69629 (p : Pattern) (ha : d128217 p = 1) (hb : d277740 p = 1) : d277965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16017 q = 1) (hb : d277740 q = 1) : d277954 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16017, d277954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69628 q ha hb
    | true =>
      simp only [d16017, d277954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69600 q ha hb
  have h2 (q : Pattern) (ha : d128213 q = 1) (hb : d277740 q = 1) : d277955 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128213, d277955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128213, d277955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5378 q = 1) (hb : d277740 q = 1) : d277960 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5378, d277960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69625 q ha hb
    | true =>
      simp only [d5378, d277960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5379 q = 1) (hb : d277740 q = 1) : d277961 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5379, d277961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5379, d277961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128214 q = 1) (hb : d277740 q = 1) : d277962 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128214, d277962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128214, d277962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128215 q = 1) (hb : d277740 q = 1) : d277963 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128215, d277963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128215, d277963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128216 q = 1) (hb : d277740 q = 1) : d277964 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128216, d277964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128216, d277964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128217 q = 1) (hb : d277740 q = 1) : d277965 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128217, d277965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128217, d277965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69630 (p : Pattern) (ha : d128223 p = 1) (hb : d277740 p = 1) : d277971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d285 q = 1) (hb : d277740 q = 1) : d277831 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, d277831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d285, d277831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69606 q ha hb
  have h2 (q : Pattern) (ha : d286 q = 1) (hb : d277740 q = 1) : d277832 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, d277832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d286, d277832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d292 q = 1) (hb : d277740 q = 1) : d277838 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, d277838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69606 q ha hb
    | true =>
      simp only [d292, d277838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69607 q ha hb
  have h4 (q : Pattern) (ha : d293 q = 1) (hb : d277740 q = 1) : d277839 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, d277839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d293, d277839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d294 q = 1) (hb : d277740 q = 1) : d277840 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, d277840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d294, d277840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128201 q = 1) (hb : d277740 q = 1) : d277917 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128201, d277917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69618 q ha hb
    | true =>
      simp only [d128201, d277917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69623 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d277740 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d398 q = 1) (hb : d277740 q = 1) : d277919 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, d277919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69608 q ha hb
    | true =>
      simp only [d398, d277919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128202 q = 1) (hb : d277740 q = 1) : d277920 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128202, d277920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128202, d277920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128203 q = 1) (hb : d277740 q = 1) : d277921 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128203, d277921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128203, d277921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d128204 q = 1) (hb : d277740 q = 1) : d277922 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128204, d277922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128204, d277922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128208 q = 1) (hb : d277740 q = 1) : d277926 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128208, d277926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128208, d277926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69624 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d277740 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d128209 q = 1) (hb : d277740 q = 1) : d277927 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128209, d277927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d128209, d277927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128210 q = 1) (hb : d277740 q = 1) : d277928 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128210, d277928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128210, d277928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128211 q = 1) (hb : d277740 q = 1) : d277929 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128211, d277929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d128211, d277929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d128212 q = 1) (hb : d277740 q = 1) : d277930 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128212, d277930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128212, d277930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d128218 q = 1) (hb : d277740 q = 1) : d277966 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128218, d277966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128218, d277966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69629 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d277740 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d128219 q = 1) (hb : d277740 q = 1) : d277967 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128219, d277967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128219, d277967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d128220 q = 1) (hb : d277740 q = 1) : d277968 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128220, d277968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128220, d277968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128221 q = 1) (hb : d277740 q = 1) : d277969 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128221, d277969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128221, d277969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128222 q = 1) (hb : d277740 q = 1) : d277970 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128222, d277970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128222, d277970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d128223 q = 1) (hb : d277740 q = 1) : d277971 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128223, d277971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128223, d277971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro69631 (p : Pattern) (ha : d128229 p = 1) (hb : d277740 p = 1) : d277977 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d277740 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d51653 q = 1) (hb : d277740 q = 1) : d277821 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d51653, d277821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51653, d277821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69605 q ha hb
  have h3 (q : Pattern) (ha : d51654 q = 1) (hb : d277740 q = 1) : d277822 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d51654, d277822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51654, d277822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51655 q = 1) (hb : d277740 q = 1) : d277823 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d51655, d277823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51655, d277823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d51656 q = 1) (hb : d277740 q = 1) : d277824 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d51656, d277824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d51656, d277824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51657 q = 1) (hb : d277740 q = 1) : d277825 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d51657, d277825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d51657, d277825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128224 q = 1) (hb : d277740 q = 1) : d277972 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128224, d277972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128224, d277972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69630 q ha hb
  have h8 (q : Pattern) (ha : d128225 q = 1) (hb : d277740 q = 1) : d277973 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128225, d277973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128225, d277973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128226 q = 1) (hb : d277740 q = 1) : d277974 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128226, d277974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128226, d277974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d128227 q = 1) (hb : d277740 q = 1) : d277975 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128227, d277975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128227, d277975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128228 q = 1) (hb : d277740 q = 1) : d277976 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128228, d277976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128228, d277976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d128229 q = 1) (hb : d277740 q = 1) : d277977 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128229, d277977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128229, d277977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro69632 (p : Pattern) (ha : d481 p = 1) (hb : d277740 p = 1) : d277984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d277740 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d145 q = 1) (hb : d277740 q = 1) : d277754 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d277754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69594 q ha hb
    | true =>
      simp only [d145, d277754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d146 q = 1) (hb : d277740 q = 1) : d277755 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d277755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d277755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147 q = 1) (hb : d277740 q = 1) : d277756 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d277756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d277756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d475 q = 1) (hb : d277740 q = 1) : d277978 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d277978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d475, d277978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d480 q = 1) (hb : d277740 q = 1) : d277983 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d277983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d480, d277983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d481 q = 1) (hb : d277740 q = 1) : d277984 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d481, d277984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d481, d277984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro69633 (p : Pattern) (ha : d491 p = 1) (hb : d277740 p = 1) : d277994 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d277740 q = 1) : d277985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69632 q ha hb
    | true =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d277740 q = 1) : d277986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d277740 q = 1) : d277991 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d277991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d277991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d277740 q = 1) : d277992 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d277992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d277992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d277740 q = 1) : d277993 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d277993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d277993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d491 q = 1) (hb : d277740 q = 1) : d277994 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d491, d277994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d491, d277994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69634 (p : Pattern) (ha : d501 p = 1) (hb : d277740 p = 1) : d278004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d277740 q = 1) : d277985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69632 q ha hb
    | true =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d277740 q = 1) : d277986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d277740 q = 1) : d277991 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d277991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d277991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d277740 q = 1) : d277992 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d277992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d277992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d490 q = 1) (hb : d277740 q = 1) : d277993 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d490, d277993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d490, d277993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d501 q = 1) (hb : d277740 q = 1) : d278004 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d501, d278004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d501, d278004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69635 (p : Pattern) (ha : d644 p = 1) (hb : d277740 p = 1) : d278115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d633 q = 1) (hb : d277740 q = 1) : d278104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d278104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69633 q ha hb
    | true =>
      simp only [d633, d278104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d634 q = 1) (hb : d277740 q = 1) : d278105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d278105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d278105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d635 q = 1) (hb : d277740 q = 1) : d278106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d278106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d635, d278106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d636 q = 1) (hb : d277740 q = 1) : d278107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d278107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d278107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d637 q = 1) (hb : d277740 q = 1) : d278108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d278108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d278108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d639 q = 1) (hb : d277740 q = 1) : d278110 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d278110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69634 q ha hb
    | true =>
      simp only [d639, d278110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d640 q = 1) (hb : d277740 q = 1) : d278111 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d278111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d278111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d641 q = 1) (hb : d277740 q = 1) : d278112 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d278112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d641, d278112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d642 q = 1) (hb : d277740 q = 1) : d278113 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d278113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d278113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d643 q = 1) (hb : d277740 q = 1) : d278114 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d278114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d278114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d644 q = 1) (hb : d277740 q = 1) : d278115 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d644, d278115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d644, d278115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro69636 (p : Pattern) (ha : d653 p = 1) (hb : d277740 p = 1) : d278124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d639 q = 1) (hb : d277740 q = 1) : d278110 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d639, d278110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69634 q ha hb
    | true =>
      simp only [d639, d278110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d640 q = 1) (hb : d277740 q = 1) : d278111 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d640, d278111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d640, d278111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d641 q = 1) (hb : d277740 q = 1) : d278112 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d641, d278112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d641, d278112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d642 q = 1) (hb : d277740 q = 1) : d278113 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d642, d278113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d642, d278113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d643 q = 1) (hb : d277740 q = 1) : d278114 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d643, d278114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d643, d278114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d653 q = 1) (hb : d277740 q = 1) : d278124 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d653, d278124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d653, d278124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69637 (p : Pattern) (ha : d683 p = 1) (hb : d277740 p = 1) : d278167 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d277740 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d232 q = 1) (hb : d277740 q = 1) : d277797 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d277797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69598 q ha hb
    | true =>
      simp only [d232, d277797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d233 q = 1) (hb : d277740 q = 1) : d277798 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d277798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d277798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d234 q = 1) (hb : d277740 q = 1) : d277799 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d277799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d277799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d673 q = 1) (hb : d277740 q = 1) : d278157 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d278157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d673, d278157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d682 q = 1) (hb : d277740 q = 1) : d278166 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d682, d278166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d682, d278166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d683 q = 1) (hb : d277740 q = 1) : d278167 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d683, d278167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d683, d278167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro69638 (p : Pattern) (ha : d730 p = 1) (hb : d277740 p = 1) : d278190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d684 q = 1) (hb : d277740 q = 1) : d278168 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d278168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69637 q ha hb
    | true =>
      simp only [d684, d278168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d685 q = 1) (hb : d277740 q = 1) : d278169 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d278169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d278169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d727 q = 1) (hb : d277740 q = 1) : d278187 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d727, d278187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d727, d278187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d728 q = 1) (hb : d277740 q = 1) : d278188 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d728, d278188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d728, d278188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d729 q = 1) (hb : d277740 q = 1) : d278189 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d729, d278189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d729, d278189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d730 q = 1) (hb : d277740 q = 1) : d278190 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d730, d278190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d730, d278190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69639 (p : Pattern) (ha : d736 p = 1) (hb : d277740 p = 1) : d278196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d731 q = 1) (hb : d277740 q = 1) : d278191 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d731, d278191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69638 q ha hb
    | true =>
      simp only [d731, d278191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d732 q = 1) (hb : d277740 q = 1) : d278192 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d732, d278192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d732, d278192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d733 q = 1) (hb : d277740 q = 1) : d278193 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d733, d278193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d733, d278193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d734 q = 1) (hb : d277740 q = 1) : d278194 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d734, d278194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d734, d278194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d735 q = 1) (hb : d277740 q = 1) : d278195 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d735, d278195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d735, d278195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d736 q = 1) (hb : d277740 q = 1) : d278196 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d736, d278196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d736, d278196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69640 (p : Pattern) (ha : d16036 p = 1) (hb : d277740 p = 1) : d277980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d277740 q = 1) : d277874 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d277874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69615 q ha hb
    | true =>
      simp only [d15967, d277874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69594 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d277740 q = 1) : d277875 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d277875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d277875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d277740 q = 1) : d277876 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d277876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d277876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d277740 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d145 q = 1) (hb : d277740 q = 1) : d277754 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d277754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69594 q ha hb
    | true =>
      simp only [d145, d277754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d146 q = 1) (hb : d277740 q = 1) : d277755 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d277755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d277755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147 q = 1) (hb : d277740 q = 1) : d277756 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d277756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d277756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15970 q = 1) (hb : d277740 q = 1) : d277877 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d277877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d277877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d475 q = 1) (hb : d277740 q = 1) : d277978 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d277978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d475, d277978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16035 q = 1) (hb : d277740 q = 1) : d277979 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16035, d277979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16035, d277979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16036 q = 1) (hb : d277740 q = 1) : d277980 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16036, d277980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16036, d277980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro69641 (p : Pattern) (ha : d16042 p = 1) (hb : d277740 p = 1) : d277990 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d277740 q = 1) : d277981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69640 q ha hb
    | true =>
      simp only [d16037, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d277740 q = 1) : d277982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d277740 q = 1) : d277985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69632 q ha hb
    | true =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d277740 q = 1) : d277986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d277740 q = 1) : d277987 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d277987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d277987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d277740 q = 1) : d277988 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d277988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d277988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d277740 q = 1) : d277989 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d277989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d277989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16042 q = 1) (hb : d277740 q = 1) : d277990 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16042, d277990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16042, d277990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69642 (p : Pattern) (ha : d16048 p = 1) (hb : d277740 p = 1) : d278000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d277740 q = 1) : d277995 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d277995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69641 q ha hb
    | true =>
      simp only [d16043, d277995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69633 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d277740 q = 1) : d277996 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d277996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d277996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d277740 q = 1) : d277997 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d277997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d277997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d277740 q = 1) : d277998 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d277998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d277998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d277740 q = 1) : d277999 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d277999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d277999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16048 q = 1) (hb : d277740 q = 1) : d278000 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16048, d278000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16048, d278000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69643 (p : Pattern) (ha : d16051 p = 1) (hb : d277740 p = 1) : d278003 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d277740 q = 1) : d277981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69640 q ha hb
    | true =>
      simp only [d16037, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d277740 q = 1) : d277982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d277740 q = 1) : d277985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69632 q ha hb
    | true =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d277740 q = 1) : d277986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d277740 q = 1) : d277987 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d277987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d277987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d277740 q = 1) : d277988 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d277988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d277988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16041 q = 1) (hb : d277740 q = 1) : d277989 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16041, d277989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16041, d277989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16051 q = 1) (hb : d277740 q = 1) : d278003 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16051, d278003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16051, d278003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro69644 (p : Pattern) (ha : d16057 p = 1) (hb : d277740 p = 1) : d278010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d277740 q = 1) : d277995 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d277995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69641 q ha hb
    | true =>
      simp only [d16043, d277995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69633 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d277740 q = 1) : d277996 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d277996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d277996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d277740 q = 1) : d277997 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d277997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d277997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d277740 q = 1) : d277998 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d277998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d277998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d277740 q = 1) : d277999 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d277999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d277999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16052 q = 1) (hb : d277740 q = 1) : d278005 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16052, d278005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69643 q ha hb
    | true =>
      simp only [d16052, d278005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69634 q ha hb
  have h7 (q : Pattern) (ha : d16053 q = 1) (hb : d277740 q = 1) : d278006 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16053, d278006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16053, d278006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16054 q = 1) (hb : d277740 q = 1) : d278007 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16054, d278007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16054, d278007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16055 q = 1) (hb : d277740 q = 1) : d278008 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16055, d278008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16055, d278008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16056 q = 1) (hb : d277740 q = 1) : d278009 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16056, d278009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16056, d278009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16057 q = 1) (hb : d277740 q = 1) : d278010 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16057, d278010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16057, d278010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro69645 (p : Pattern) (ha : d16143 p = 1) (hb : d277740 p = 1) : d278109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16043 q = 1) (hb : d277740 q = 1) : d277995 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16043, d277995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69641 q ha hb
    | true =>
      simp only [d16043, d277995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69633 q ha hb
  have h2 (q : Pattern) (ha : d16044 q = 1) (hb : d277740 q = 1) : d277996 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16044, d277996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16044, d277996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16045 q = 1) (hb : d277740 q = 1) : d277997 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16045, d277997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16045, d277997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16046 q = 1) (hb : d277740 q = 1) : d277998 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16046, d277998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16046, d277998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16047 q = 1) (hb : d277740 q = 1) : d277999 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16047, d277999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16047, d277999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d633 q = 1) (hb : d277740 q = 1) : d278104 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d278104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69633 q ha hb
    | true =>
      simp only [d633, d278104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d634 q = 1) (hb : d277740 q = 1) : d278105 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, d278105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, d278105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d635 q = 1) (hb : d277740 q = 1) : d278106 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, d278106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d635, d278106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d636 q = 1) (hb : d277740 q = 1) : d278107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, d278107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, d278107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d637 q = 1) (hb : d277740 q = 1) : d278108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, d278108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, d278108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16143 q = 1) (hb : d277740 q = 1) : d278109 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16143, d278109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16143, d278109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro69646 (p : Pattern) (ha : d514 p = 1) (hb : d277740 p = 1) : d278017 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d277740 q = 1) : d277985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69632 q ha hb
    | true =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d277740 q = 1) : d277986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d277740 q = 1) : d277991 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d277991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d277991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d277740 q = 1) : d277992 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d277992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d277992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d277740 q = 1) : d278016 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d278016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d278016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d514 q = 1) (hb : d277740 q = 1) : d278017 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d514, d278017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d514, d278017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69647 (p : Pattern) (ha : d524 p = 1) (hb : d277740 p = 1) : d278027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d277740 q = 1) : d277985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69632 q ha hb
    | true =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d277740 q = 1) : d277986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d277740 q = 1) : d277991 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d277991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d277991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d277740 q = 1) : d278025 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d278025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d278025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d277740 q = 1) : d278026 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d278026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d278026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d277740 q = 1) : d278027 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d524, d278027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d524, d278027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69648 (p : Pattern) (ha : d16062 p = 1) (hb : d277740 p = 1) : d278015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d277740 q = 1) : d277981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69640 q ha hb
    | true =>
      simp only [d16037, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d277740 q = 1) : d277982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d277740 q = 1) : d277985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69632 q ha hb
    | true =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d277740 q = 1) : d277986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d277740 q = 1) : d277987 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d277987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d277987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d277740 q = 1) : d277988 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d277988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d277988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d277740 q = 1) : d278014 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d278014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d278014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16062 q = 1) (hb : d277740 q = 1) : d278015 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16062, d278015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16062, d278015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69649 (p : Pattern) (ha : d16069 p = 1) (hb : d277740 p = 1) : d278024 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d277740 q = 1) : d277981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69640 q ha hb
    | true =>
      simp only [d16037, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d277740 q = 1) : d277982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d277740 q = 1) : d277985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69632 q ha hb
    | true =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d277740 q = 1) : d277986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d277740 q = 1) : d277987 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d277987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d277987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d277740 q = 1) : d278022 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d278022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d278022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d277740 q = 1) : d278023 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d278023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d278023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16069 q = 1) (hb : d277740 q = 1) : d278024 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16069, d278024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16069, d278024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69650 (p : Pattern) (ha : d530 p = 1) (hb : d277739 p = 1) : d34352 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d309 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d528 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d528, d216468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d528, d216468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d310 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d529 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d529, d277739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d529, d277739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d309 q = 1) : d309 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d129 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310 q = 1) (hb : d216468 q = 1) : d825 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d130 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d311 q = 1) (hb : d277739 q = 1) : d5121 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d311, d277739, d5121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d311, d277739, d5121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d530 q = 1) (hb : d277739 q = 1) : d34352 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d530, d34352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d530, d34352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro69651 (p : Pattern) (ha : d536 p = 1) (hb : d277739 p = 1) : d277853 p = 1 := by
  have h0 (q : Pattern) (ha : d1 q = 1) (hb : d309 q = 1) : d309 q = 1 := by
    exact hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d310 q = 1) (hb : d216468 q = 1) : d825 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d534 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d535 q = 1) (hb : d277739 q = 1) : d5121 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d535, d277739, d5121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d535, d277739, d5121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d129 q = 1) : d129 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d15 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d130 q = 1) (hb : d216468 q = 1) : d534 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d130, d216468, d534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d130, d216468, d534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d16 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d131 q = 1) (hb : d277739 q = 1) : d33559 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d131, d277739, d33559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d131, d277739, d33559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d536 q = 1) (hb : d277739 q = 1) : d277853 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d536, d277853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d536, d277853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro69652 (p : Pattern) (ha : d542 p = 1) (hb : d277740 p = 1) : d278034 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d277739 q = 1) : d34353 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d34353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69650 q ha hb
    | true =>
      simp only [d531, d34353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d532 q = 1) (hb : d277740 q = 1) : d34354 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d277740, d34354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d277740, d34354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d313 q = 1) (hb : d277739 q = 1) : d277854 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69612 q ha hb
    | true =>
      simp only [d313, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d314 q = 1) (hb : d277740 q = 1) : d277855 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d314, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d533 q = 1) (hb : d277740 q = 1) : d278031 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d278031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d533, d278031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d537 q = 1) (hb : d277739 q = 1) : d277854 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69651 q ha hb
    | true =>
      simp only [d537, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d538 q = 1) (hb : d277740 q = 1) : d277855 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d538, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d133 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69592 q ha hb
    | true =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d134 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d539 q = 1) (hb : d277740 q = 1) : d277856 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d539, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d540 q = 1) (hb : d277740 q = 1) : d278032 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d540, d278032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d540, d278032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d541 q = 1) (hb : d277740 q = 1) : d278033 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d541, d278033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d541, d278033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d315 q = 1) (hb : d277740 q = 1) : d277856 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d315, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h16 (q : Pattern) (ha : d20 q = 1) (hb : d277740 q = 1) : d20 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d135 q = 1) (hb : d277740 q = 1) : d277744 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d135, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d316 q = 1) (hb : d277740 q = 1) : d277857 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d277857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d316, d277857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d317 q = 1) (hb : d277740 q = 1) : d277858 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d277858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d317, d277858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h20 (q : Pattern) (ha : d542 q = 1) (hb : d277740 q = 1) : d278034 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d542, d278034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d542, d278034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro69653 (p : Pattern) (ha : d5011 p = 1) (hb : d277739 p = 1) : d277741 p = 1 := by
  have h0 (q : Pattern) (ha : d534 q = 1) (hb : d216468 q = 1) : d534 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d16 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5010 q = 1) (hb : d277739 q = 1) : d33559 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d5010, d277739, d33559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5010, d277739, d33559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d17 q = 1) (hb : d277739 q = 1) : d17 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5011 q = 1) (hb : d277739 q = 1) : d277741 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d5011, d277741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5011, d277741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro69654 (p : Pattern) (ha : d9457 p = 1) (hb : d277740 p = 1) : d278039 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d277739 q = 1) : d277854 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69612 q ha hb
    | true =>
      simp only [d313, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d277740 q = 1) : d277855 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d133 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69592 q ha hb
    | true =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d134 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d315 q = 1) (hb : d277740 q = 1) : d277856 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d315, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d315, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d20 q = 1) (hb : d277740 q = 1) : d20 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d135 q = 1) (hb : d277740 q = 1) : d277744 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d135, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d316 q = 1) (hb : d277740 q = 1) : d277857 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d316, d277857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d316, d277857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d317 q = 1) (hb : d277740 q = 1) : d277858 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d317, d277858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d317, d277858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9452 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69653 q ha hb
    | true =>
      simp only [d9452, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d9453 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9453, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d9454 q = 1) (hb : d277740 q = 1) : d277744 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9454, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9454, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d9455 q = 1) (hb : d277740 q = 1) : d277865 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9455, d277865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9455, d277865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h16 (q : Pattern) (ha : d9456 q = 1) (hb : d277740 q = 1) : d277866 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9456, d277866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9456, d277866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h17 (q : Pattern) (ha : d9457 q = 1) (hb : d277740 q = 1) : d278039 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9457, d278039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9457, d278039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro69655 (p : Pattern) (ha : d9467 p = 1) (hb : d277740 p = 1) : d278047 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d313 q = 1) (hb : d277739 q = 1) : d277854 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69612 q ha hb
    | true =>
      simp only [d313, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d314 q = 1) (hb : d277740 q = 1) : d277855 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d314, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9452 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69653 q ha hb
    | true =>
      simp only [d9452, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9453 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9453, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d9464 q = 1) (hb : d277740 q = 1) : d277856 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9464, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9464, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9465 q = 1) (hb : d277740 q = 1) : d278045 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9465, d278045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9465, d278045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9466 q = 1) (hb : d277740 q = 1) : d278046 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9466, d278046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9466, d278046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d20 q = 1) (hb : d277740 q = 1) : d20 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9454 q = 1) (hb : d277740 q = 1) : d277744 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9454, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9454, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9455 q = 1) (hb : d277740 q = 1) : d277865 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9455, d277865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9455, d277865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h13 (q : Pattern) (ha : d9456 q = 1) (hb : d277740 q = 1) : d277866 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9456, d277866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9456, d277866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h14 (q : Pattern) (ha : d9467 q = 1) (hb : d277740 q = 1) : d278047 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9467, d278047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9467, d278047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro69656 (p : Pattern) (ha : d16077 p = 1) (hb : d277740 p = 1) : d278053 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d277740 q = 1) : d278035 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d278035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69652 q ha hb
    | true =>
      simp only [d543, d278035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d277740 q = 1) : d278036 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d278036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d278036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d277740 q = 1) : d278037 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d278037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d278037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d277740 q = 1) : d278038 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d278038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d278038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9458 q = 1) (hb : d277740 q = 1) : d278040 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d278040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69654 q ha hb
    | true =>
      simp only [d9458, d278040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9460 q = 1) (hb : d277740 q = 1) : d278041 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d278041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9460, d278041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16073 q = 1) (hb : d277740 q = 1) : d278042 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16073, d278042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16073, d278042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16074 q = 1) (hb : d277740 q = 1) : d278043 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16074, d278043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16074, d278043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16075 q = 1) (hb : d277740 q = 1) : d278044 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, d278044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16075, d278044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9468 q = 1) (hb : d277740 q = 1) : d278048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d278048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69655 q ha hb
    | true =>
      simp only [d9468, d278048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9470 q = 1) (hb : d277740 q = 1) : d278049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d278049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9470, d278049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12748 q = 1) (hb : d277740 q = 1) : d278050 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d278050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d278050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12749 q = 1) (hb : d277740 q = 1) : d278051 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d278051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12749, d278051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9382 q = 1) (hb : d277740 q = 1) : d277868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d277868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69614 q ha hb
    | true =>
      simp only [d9382, d277868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9384 q = 1) (hb : d277740 q = 1) : d277869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d277869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9384, d277869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12493 q = 1) (hb : d277740 q = 1) : d277870 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d277870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d277870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12494 q = 1) (hb : d277740 q = 1) : d277871 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d277871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12494, d277871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16076 q = 1) (hb : d277740 q = 1) : d278052 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16076, d278052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16076, d278052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16077 q = 1) (hb : d277740 q = 1) : d278053 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16077, d278053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16077, d278053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro69657 (p : Pattern) (ha : d16081 p = 1) (hb : d277740 p = 1) : d278057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9382 q = 1) (hb : d277740 q = 1) : d277868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d277868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69614 q ha hb
    | true =>
      simp only [d9382, d277868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9384 q = 1) (hb : d277740 q = 1) : d277869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d277869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9384, d277869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12493 q = 1) (hb : d277740 q = 1) : d277870 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12493, d277870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12493, d277870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12494 q = 1) (hb : d277740 q = 1) : d277871 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12494, d277871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12494, d277871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d277740 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d12495 q = 1) (hb : d277740 q = 1) : d277872 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12495, d277872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12495, d277872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d277740 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d16081 q = 1) (hb : d277740 q = 1) : d278057 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16081, d278057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16081, d278057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69658 (p : Pattern) (ha : d16087 p = 1) (hb : d277740 p = 1) : d278063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16078 q = 1) (hb : d277740 q = 1) : d278054 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16078, d278054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69656 q ha hb
    | true =>
      simp only [d16078, d278054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69615 q ha hb
  have h2 (q : Pattern) (ha : d16079 q = 1) (hb : d277740 q = 1) : d278055 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16079, d278055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16079, d278055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16080 q = 1) (hb : d277740 q = 1) : d278056 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16080, d278056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16080, d278056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16082 q = 1) (hb : d277740 q = 1) : d278058 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16082, d278058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69615 q ha hb
    | true =>
      simp only [d16082, d278058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69657 q ha hb
  have h5 (q : Pattern) (ha : d16083 q = 1) (hb : d277740 q = 1) : d278059 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16083, d278059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16083, d278059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16084 q = 1) (hb : d277740 q = 1) : d278060 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16084, d278060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16084, d278060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16085 q = 1) (hb : d277740 q = 1) : d278061 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16085, d278061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16085, d278061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15967 q = 1) (hb : d277740 q = 1) : d277874 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d277874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69615 q ha hb
    | true =>
      simp only [d15967, d277874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69594 q ha hb
  have h9 (q : Pattern) (ha : d15968 q = 1) (hb : d277740 q = 1) : d277875 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d277875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d277875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15969 q = 1) (hb : d277740 q = 1) : d277876 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d277876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d277876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30 q = 1) (hb : d277740 q = 1) : d30 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d145 q = 1) (hb : d277740 q = 1) : d277754 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d277754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69594 q ha hb
    | true =>
      simp only [d145, d277754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d146 q = 1) (hb : d277740 q = 1) : d277755 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d277755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d277755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147 q = 1) (hb : d277740 q = 1) : d277756 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d277756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d277756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d15970 q = 1) (hb : d277740 q = 1) : d277877 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d277877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15970, d277877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16086 q = 1) (hb : d277740 q = 1) : d278062 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16086, d278062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16086, d278062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16087 q = 1) (hb : d277740 q = 1) : d278063 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16087, d278063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16087, d278063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro69659 (p : Pattern) (ha : d16093 p = 1) (hb : d277740 p = 1) : d278069 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16088 q = 1) (hb : d277740 q = 1) : d278064 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16088, d278064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69658 q ha hb
    | true =>
      simp only [d16088, d278064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16089 q = 1) (hb : d277740 q = 1) : d278065 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16089, d278065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16089, d278065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d277740 q = 1) : d277981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69640 q ha hb
    | true =>
      simp only [d16037, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d277740 q = 1) : d277982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16090 q = 1) (hb : d277740 q = 1) : d278066 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16090, d278066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16090, d278066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16091 q = 1) (hb : d277740 q = 1) : d278067 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16091, d278067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16091, d278067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16092 q = 1) (hb : d277740 q = 1) : d278068 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16092, d278068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16092, d278068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16093 q = 1) (hb : d277740 q = 1) : d278069 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16093, d278069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16093, d278069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69660 (p : Pattern) (ha : d16114 p = 1) (hb : d277740 p = 1) : d278075 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d277740 q = 1) : d277981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69640 q ha hb
    | true =>
      simp only [d16037, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d277740 q = 1) : d277982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d277740 q = 1) : d278072 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d278072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d278072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d277740 q = 1) : d278073 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d278073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d278073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d277740 q = 1) : d278074 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d278074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d278074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16114 q = 1) (hb : d277740 q = 1) : d278075 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16114, d278075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16114, d278075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69661 (p : Pattern) (ha : d128234 p = 1) (hb : d277740 p = 1) : d278081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d277740 q = 1) : d278018 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d278018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69648 q ha hb
    | true =>
      simp only [d16063, d278018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69646 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d277740 q = 1) : d278019 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d278019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d278019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d277740 q = 1) : d278020 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d278020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d278020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d277740 q = 1) : d278021 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d278021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d278021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d277740 q = 1) : d278028 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d278028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69649 q ha hb
    | true =>
      simp only [d16070, d278028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69647 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d277740 q = 1) : d278029 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d278029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d278029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d277740 q = 1) : d278030 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d278030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d278030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16094 q = 1) (hb : d277740 q = 1) : d278070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16094, d278070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69659 q ha hb
    | true =>
      simp only [d16094, d278070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69641 q ha hb
  have h9 (q : Pattern) (ha : d128230 q = 1) (hb : d277740 q = 1) : d278071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128230, d278071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128230, d278071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d277740 q = 1) : d278076 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d278076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69660 q ha hb
    | true =>
      simp only [d16115, d278076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d277740 q = 1) : d278077 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d278077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d278077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128231 q = 1) (hb : d277740 q = 1) : d278078 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128231, d278078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128231, d278078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128232 q = 1) (hb : d277740 q = 1) : d278079 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128232, d278079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128232, d278079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128233 q = 1) (hb : d277740 q = 1) : d278080 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128233, d278080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128233, d278080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128234 q = 1) (hb : d277740 q = 1) : d278081 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128234, d278081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128234, d278081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro69662 (p : Pattern) (ha : d610 p = 1) (hb : d277740 p = 1) : d278083 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d277740 q = 1) : d277985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69632 q ha hb
    | true =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d277740 q = 1) : d277986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d277740 q = 1) : d277991 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d277991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d277991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d489 q = 1) (hb : d277740 q = 1) : d277992 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d489, d277992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d489, d277992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d513 q = 1) (hb : d277740 q = 1) : d278016 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d513, d278016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d513, d278016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d610 q = 1) (hb : d277740 q = 1) : d278083 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d610, d278083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d610, d278083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69663 (p : Pattern) (ha : d616 p = 1) (hb : d277740 p = 1) : d278089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d482 q = 1) (hb : d277740 q = 1) : d277985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69632 q ha hb
    | true =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d277740 q = 1) : d277986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d488 q = 1) (hb : d277740 q = 1) : d277991 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d488, d277991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d488, d277991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d522 q = 1) (hb : d277740 q = 1) : d278025 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d522, d278025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d522, d278025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d523 q = 1) (hb : d277740 q = 1) : d278026 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d523, d278026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d523, d278026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d616 q = 1) (hb : d277740 q = 1) : d278089 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d616, d278089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d616, d278089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69664 (p : Pattern) (ha : d16121 p = 1) (hb : d277740 p = 1) : d278082 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d277740 q = 1) : d277981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69640 q ha hb
    | true =>
      simp only [d16037, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d277740 q = 1) : d277982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d277740 q = 1) : d277985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69632 q ha hb
    | true =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d277740 q = 1) : d277986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d277740 q = 1) : d277987 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d277987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d277987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16040 q = 1) (hb : d277740 q = 1) : d277988 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16040, d277988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16040, d277988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16061 q = 1) (hb : d277740 q = 1) : d278014 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16061, d278014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16061, d278014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16121 q = 1) (hb : d277740 q = 1) : d278082 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16121, d278082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16121, d278082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro69665 (p : Pattern) (ha : d16126 p = 1) (hb : d277740 p = 1) : d278088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d277740 q = 1) : d277981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69640 q ha hb
    | true =>
      simp only [d16037, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d277740 q = 1) : d277982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d482 q = 1) (hb : d277740 q = 1) : d277985 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69632 q ha hb
    | true =>
      simp only [d482, d277985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d483 q = 1) (hb : d277740 q = 1) : d277986 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d277986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16039 q = 1) (hb : d277740 q = 1) : d277987 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16039, d277987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16039, d277987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16067 q = 1) (hb : d277740 q = 1) : d278022 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16067, d278022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16067, d278022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16068 q = 1) (hb : d277740 q = 1) : d278023 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16068, d278023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16068, d278023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16126 q = 1) (hb : d277740 q = 1) : d278088 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16126, d278088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16126, d278088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro69666 (p : Pattern) (ha : d16130 p = 1) (hb : d277740 p = 1) : d278093 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16088 q = 1) (hb : d277740 q = 1) : d278064 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16088, d278064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69658 q ha hb
    | true =>
      simp only [d16088, d278064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16089 q = 1) (hb : d277740 q = 1) : d278065 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16089, d278065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16089, d278065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16037 q = 1) (hb : d277740 q = 1) : d277981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69640 q ha hb
    | true =>
      simp only [d16037, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16038 q = 1) (hb : d277740 q = 1) : d277982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16090 q = 1) (hb : d277740 q = 1) : d278066 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16090, d278066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16090, d278066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16091 q = 1) (hb : d277740 q = 1) : d278067 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16091, d278067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16091, d278067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16092 q = 1) (hb : d277740 q = 1) : d278068 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16092, d278068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16092, d278068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16130 q = 1) (hb : d277740 q = 1) : d278093 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16130, d278093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16130, d278093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro69667 (p : Pattern) (ha : d16135 p = 1) (hb : d277740 p = 1) : d278096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16037 q = 1) (hb : d277740 q = 1) : d277981 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16037, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69640 q ha hb
    | true =>
      simp only [d16037, d277981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16038 q = 1) (hb : d277740 q = 1) : d277982 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16038, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16038, d277982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16111 q = 1) (hb : d277740 q = 1) : d278072 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16111, d278072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16111, d278072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16112 q = 1) (hb : d277740 q = 1) : d278073 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16112, d278073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16112, d278073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16113 q = 1) (hb : d277740 q = 1) : d278074 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16113, d278074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16113, d278074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16135 q = 1) (hb : d277740 q = 1) : d278096 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16135, d278096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16135, d278096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69668 (p : Pattern) (ha : d128239 p = 1) (hb : d277740 p = 1) : d278102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16063 q = 1) (hb : d277740 q = 1) : d278018 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16063, d278018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69648 q ha hb
    | true =>
      simp only [d16063, d278018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69646 q ha hb
  have h2 (q : Pattern) (ha : d16064 q = 1) (hb : d277740 q = 1) : d278019 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16064, d278019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16064, d278019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16065 q = 1) (hb : d277740 q = 1) : d278020 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16065, d278020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16065, d278020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16066 q = 1) (hb : d277740 q = 1) : d278021 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16066, d278021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16066, d278021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16070 q = 1) (hb : d277740 q = 1) : d278028 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16070, d278028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69649 q ha hb
    | true =>
      simp only [d16070, d278028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69647 q ha hb
  have h6 (q : Pattern) (ha : d16071 q = 1) (hb : d277740 q = 1) : d278029 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16071, d278029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16071, d278029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16072 q = 1) (hb : d277740 q = 1) : d278030 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16072, d278030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16072, d278030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16094 q = 1) (hb : d277740 q = 1) : d278070 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16094, d278070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69659 q ha hb
    | true =>
      simp only [d16094, d278070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69641 q ha hb
  have h9 (q : Pattern) (ha : d128230 q = 1) (hb : d277740 q = 1) : d278071 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128230, d278071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128230, d278071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16115 q = 1) (hb : d277740 q = 1) : d278076 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16115, d278076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69660 q ha hb
    | true =>
      simp only [d16115, d278076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16116 q = 1) (hb : d277740 q = 1) : d278077 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16116, d278077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16116, d278077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128231 q = 1) (hb : d277740 q = 1) : d278078 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128231, d278078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128231, d278078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128232 q = 1) (hb : d277740 q = 1) : d278079 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128232, d278079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128232, d278079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128233 q = 1) (hb : d277740 q = 1) : d278080 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128233, d278080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128233, d278080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16122 q = 1) (hb : d277740 q = 1) : d278084 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16122, d278084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69664 q ha hb
    | true =>
      simp only [d16122, d278084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69662 q ha hb
  have h16 (q : Pattern) (ha : d16123 q = 1) (hb : d277740 q = 1) : d278085 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16123, d278085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16123, d278085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16124 q = 1) (hb : d277740 q = 1) : d278086 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16124, d278086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16124, d278086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16125 q = 1) (hb : d277740 q = 1) : d278087 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16125, d278087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16125, d278087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16127 q = 1) (hb : d277740 q = 1) : d278090 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16127, d278090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69665 q ha hb
    | true =>
      simp only [d16127, d278090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69663 q ha hb
  have h20 (q : Pattern) (ha : d16128 q = 1) (hb : d277740 q = 1) : d278091 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16128, d278091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16128, d278091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16129 q = 1) (hb : d277740 q = 1) : d278092 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16129, d278092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16129, d278092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16131 q = 1) (hb : d277740 q = 1) : d278094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16131, d278094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69666 q ha hb
    | true =>
      simp only [d16131, d278094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69643 q ha hb
  have h23 (q : Pattern) (ha : d128235 q = 1) (hb : d277740 q = 1) : d278095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128235, d278095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128235, d278095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16136 q = 1) (hb : d277740 q = 1) : d278097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d278097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69667 q ha hb
    | true =>
      simp only [d16136, d278097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16137 q = 1) (hb : d277740 q = 1) : d278098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d278098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16137, d278098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128236 q = 1) (hb : d277740 q = 1) : d278099 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128236, d278099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128236, d278099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128237 q = 1) (hb : d277740 q = 1) : d278100 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128237, d278100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128237, d278100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128238 q = 1) (hb : d277740 q = 1) : d278101 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128238, d278101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128238, d278101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128239 q = 1) (hb : d277740 q = 1) : d278102 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128239, d278102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128239, d278102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro69669 (p : Pattern) (ha : d128246 p = 1) (hb : d277740 p = 1) : d278122 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16131 q = 1) (hb : d277740 q = 1) : d278094 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16131, d278094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69666 q ha hb
    | true =>
      simp only [d16131, d278094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69643 q ha hb
  have h2 (q : Pattern) (ha : d128235 q = 1) (hb : d277740 q = 1) : d278095 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128235, d278095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128235, d278095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16136 q = 1) (hb : d277740 q = 1) : d278097 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16136, d278097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69667 q ha hb
    | true =>
      simp only [d16136, d278097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16137 q = 1) (hb : d277740 q = 1) : d278098 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16137, d278098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16137, d278098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128236 q = 1) (hb : d277740 q = 1) : d278099 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128236, d278099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128236, d278099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128244 q = 1) (hb : d277740 q = 1) : d278120 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128244, d278120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128244, d278120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128245 q = 1) (hb : d277740 q = 1) : d278121 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128245, d278121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128245, d278121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128246 q = 1) (hb : d277740 q = 1) : d278122 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128246, d278122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128246, d278122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69670 (p : Pattern) (ha : d16162 p = 1) (hb : d277740 p = 1) : d278144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d277740 q = 1) : d278130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d278130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d278130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69652 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d277740 q = 1) : d278035 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d278035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69652 q ha hb
    | true =>
      simp only [d543, d278035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d277740 q = 1) : d278131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d278131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d278131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d277740 q = 1) : d278036 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d278036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d278036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d661 q = 1) (hb : d277740 q = 1) : d278132 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d278132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d661, d278132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d662 q = 1) (hb : d277740 q = 1) : d278133 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d278133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d662, d278133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16156 q = 1) (hb : d277740 q = 1) : d278134 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d278134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16156, d278134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69654 q ha hb
  have h8 (q : Pattern) (ha : d9458 q = 1) (hb : d277740 q = 1) : d278040 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d278040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69654 q ha hb
    | true =>
      simp only [d9458, d278040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16157 q = 1) (hb : d277740 q = 1) : d278135 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, d278135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16157, d278135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9460 q = 1) (hb : d277740 q = 1) : d278041 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d278041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9460, d278041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16158 q = 1) (hb : d277740 q = 1) : d278136 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16158, d278136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16158, d278136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16159 q = 1) (hb : d277740 q = 1) : d278137 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16159, d278137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16159, d278137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16160 q = 1) (hb : d277740 q = 1) : d278138 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16160, d278138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16160, d278138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12858 q = 1) (hb : d277740 q = 1) : d278139 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d278139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d278139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69655 q ha hb
  have h15 (q : Pattern) (ha : d9468 q = 1) (hb : d277740 q = 1) : d278048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d278048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69655 q ha hb
    | true =>
      simp only [d9468, d278048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12859 q = 1) (hb : d277740 q = 1) : d278140 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d278140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12859, d278140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9470 q = 1) (hb : d277740 q = 1) : d278049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d278049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9470, d278049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12860 q = 1) (hb : d277740 q = 1) : d278141 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d278141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12860, d278141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12861 q = 1) (hb : d277740 q = 1) : d278142 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d278142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12861, d278142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d12599 q = 1) (hb : d277740 q = 1) : d277936 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d277936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d277936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69614 q ha hb
  have h21 (q : Pattern) (ha : d9382 q = 1) (hb : d277740 q = 1) : d277868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d277868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69614 q ha hb
    | true =>
      simp only [d9382, d277868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12600 q = 1) (hb : d277740 q = 1) : d277937 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d277937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12600, d277937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9384 q = 1) (hb : d277740 q = 1) : d277869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d277869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9384, d277869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12601 q = 1) (hb : d277740 q = 1) : d277938 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d277938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d12601, d277938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12602 q = 1) (hb : d277740 q = 1) : d277939 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d277939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12602, d277939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d16161 q = 1) (hb : d277740 q = 1) : d278143 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16161, d278143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d16161, d278143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d16162 q = 1) (hb : d277740 q = 1) : d278144 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16162, d278144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16162, d278144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro69671 (p : Pattern) (ha : d16166 p = 1) (hb : d277740 p = 1) : d278148 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12599 q = 1) (hb : d277740 q = 1) : d277936 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d277936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d277936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69614 q ha hb
  have h2 (q : Pattern) (ha : d9382 q = 1) (hb : d277740 q = 1) : d277868 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9382, d277868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69614 q ha hb
    | true =>
      simp only [d9382, d277868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12600 q = 1) (hb : d277740 q = 1) : d277937 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12600, d277937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12600, d277937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9384 q = 1) (hb : d277740 q = 1) : d277869 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9384, d277869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9384, d277869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12601 q = 1) (hb : d277740 q = 1) : d277938 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12601, d277938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12601, d277938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12602 q = 1) (hb : d277740 q = 1) : d277939 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12602, d277939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12602, d277939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d277740 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d12603 q = 1) (hb : d277740 q = 1) : d277940 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12603, d277940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12603, d277940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d277740 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16166 q = 1) (hb : d277740 q = 1) : d278148 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16166, d278148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16166, d278148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro69672 (p : Pattern) (ha : d16172 p = 1) (hb : d277740 p = 1) : d278154 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16163 q = 1) (hb : d277740 q = 1) : d278145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16163, d278145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69670 q ha hb
    | true =>
      simp only [d16163, d278145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69626 q ha hb
  have h2 (q : Pattern) (ha : d16164 q = 1) (hb : d277740 q = 1) : d278146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16164, d278146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16164, d278146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16165 q = 1) (hb : d277740 q = 1) : d278147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16165, d278147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16165, d278147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16167 q = 1) (hb : d277740 q = 1) : d278149 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16167, d278149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69626 q ha hb
    | true =>
      simp only [d16167, d278149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69671 q ha hb
  have h5 (q : Pattern) (ha : d16168 q = 1) (hb : d277740 q = 1) : d278150 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16168, d278150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16168, d278150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16169 q = 1) (hb : d277740 q = 1) : d278151 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16169, d278151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16169, d278151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16170 q = 1) (hb : d277740 q = 1) : d278152 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16170, d278152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16170, d278152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16005 q = 1) (hb : d277740 q = 1) : d277942 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d277942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69626 q ha hb
    | true =>
      simp only [d16005, d277942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69598 q ha hb
  have h9 (q : Pattern) (ha : d16006 q = 1) (hb : d277740 q = 1) : d277943 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d277943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d277943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16007 q = 1) (hb : d277740 q = 1) : d277944 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d277944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d277944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d71 q = 1) (hb : d277740 q = 1) : d71 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d232 q = 1) (hb : d277740 q = 1) : d277797 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d277797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69598 q ha hb
    | true =>
      simp only [d232, d277797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d233 q = 1) (hb : d277740 q = 1) : d277798 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d277798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d277798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d234 q = 1) (hb : d277740 q = 1) : d277799 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d277799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d277799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16008 q = 1) (hb : d277740 q = 1) : d277945 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d277945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16008, d277945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16171 q = 1) (hb : d277740 q = 1) : d278153 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16171, d278153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16171, d278153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16172 q = 1) (hb : d277740 q = 1) : d278154 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16172, d278154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16172, d278154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro69673 (p : Pattern) (ha : d16176 p = 1) (hb : d277740 p = 1) : d278159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16005 q = 1) (hb : d277740 q = 1) : d277942 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16005, d277942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69626 q ha hb
    | true =>
      simp only [d16005, d277942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69598 q ha hb
  have h2 (q : Pattern) (ha : d16006 q = 1) (hb : d277740 q = 1) : d277943 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16006, d277943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16006, d277943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16007 q = 1) (hb : d277740 q = 1) : d277944 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16007, d277944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16007, d277944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d277740 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d232 q = 1) (hb : d277740 q = 1) : d277797 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d232, d277797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69598 q ha hb
    | true =>
      simp only [d232, d277797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d233 q = 1) (hb : d277740 q = 1) : d277798 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d233, d277798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d233, d277798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d234 q = 1) (hb : d277740 q = 1) : d277799 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d234, d277799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d234, d277799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16008 q = 1) (hb : d277740 q = 1) : d277945 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16008, d277945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16008, d277945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d673 q = 1) (hb : d277740 q = 1) : d278157 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d673, d278157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d673, d278157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16175 q = 1) (hb : d277740 q = 1) : d278158 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16175, d278158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d16175, d278158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16176 q = 1) (hb : d277740 q = 1) : d278159 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16176, d278159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16176, d278159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro69674 (p : Pattern) (ha : d16182 p = 1) (hb : d277740 p = 1) : d278165 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16173 q = 1) (hb : d277740 q = 1) : d278155 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16173, d278155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69672 q ha hb
    | true =>
      simp only [d16173, d278155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16174 q = 1) (hb : d277740 q = 1) : d278156 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16174, d278156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16174, d278156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16177 q = 1) (hb : d277740 q = 1) : d278160 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d278160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69673 q ha hb
    | true =>
      simp only [d16177, d278160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16178 q = 1) (hb : d277740 q = 1) : d278161 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d278161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d278161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16179 q = 1) (hb : d277740 q = 1) : d278162 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16179, d278162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16179, d278162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16180 q = 1) (hb : d277740 q = 1) : d278163 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16180, d278163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16180, d278163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16181 q = 1) (hb : d277740 q = 1) : d278164 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16181, d278164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16181, d278164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16182 q = 1) (hb : d277740 q = 1) : d278165 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16182, d278165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16182, d278165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro69675 (p : Pattern) (ha : d16186 p = 1) (hb : d277740 p = 1) : d278173 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d277740 q = 1) : d278160 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d278160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69673 q ha hb
    | true =>
      simp only [d16177, d278160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d277740 q = 1) : d278161 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d278161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d278161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d684 q = 1) (hb : d277740 q = 1) : d278168 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d278168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69637 q ha hb
    | true =>
      simp only [d684, d278168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d685 q = 1) (hb : d277740 q = 1) : d278169 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d278169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d685, d278169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16183 q = 1) (hb : d277740 q = 1) : d278170 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16183, d278170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16183, d278170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16184 q = 1) (hb : d277740 q = 1) : d278171 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16184, d278171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16184, d278171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16185 q = 1) (hb : d277740 q = 1) : d278172 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16185, d278172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16185, d278172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16186 q = 1) (hb : d277740 q = 1) : d278173 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16186, d278173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16186, d278173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro69676 (p : Pattern) (ha : d16207 p = 1) (hb : d277740 p = 1) : d278179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16177 q = 1) (hb : d277740 q = 1) : d278160 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16177, d278160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69673 q ha hb
    | true =>
      simp only [d16177, d278160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16178 q = 1) (hb : d277740 q = 1) : d278161 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16178, d278161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16178, d278161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16204 q = 1) (hb : d277740 q = 1) : d278176 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16204, d278176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16204, d278176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16205 q = 1) (hb : d277740 q = 1) : d278177 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16205, d278177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16205, d278177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16206 q = 1) (hb : d277740 q = 1) : d278178 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16206, d278178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16206, d278178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16207 q = 1) (hb : d277740 q = 1) : d278179 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16207, d278179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16207, d278179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69677 (p : Pattern) (ha : d128256 p = 1) (hb : d277740 p = 1) : d278185 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16187 q = 1) (hb : d277740 q = 1) : d278174 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16187, d278174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69674 q ha hb
    | true =>
      simp only [d16187, d278174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69675 q ha hb
  have h2 (q : Pattern) (ha : d128252 q = 1) (hb : d277740 q = 1) : d278175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128252, d278175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128252, d278175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16208 q = 1) (hb : d277740 q = 1) : d278180 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16208, d278180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69676 q ha hb
    | true =>
      simp only [d16208, d278180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16209 q = 1) (hb : d277740 q = 1) : d278181 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16209, d278181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16209, d278181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128253 q = 1) (hb : d277740 q = 1) : d278182 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128253, d278182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128253, d278182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128254 q = 1) (hb : d277740 q = 1) : d278183 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128254, d278183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128254, d278183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128255 q = 1) (hb : d277740 q = 1) : d278184 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128255, d278184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128255, d278184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128256 q = 1) (hb : d277740 q = 1) : d278185 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128256, d278185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128256, d278185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69678 (p : Pattern) (ha : d128262 p = 1) (hb : d277740 p = 1) : d278202 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16049 q = 1) (hb : d277740 q = 1) : d278001 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16049, d278001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16049, d278001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69642 q ha hb
  have h2 (q : Pattern) (ha : d16050 q = 1) (hb : d277740 q = 1) : d278002 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16050, d278002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16050, d278002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16058 q = 1) (hb : d277740 q = 1) : d278011 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16058, d278011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69642 q ha hb
    | true =>
      simp only [d16058, d278011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69644 q ha hb
  have h4 (q : Pattern) (ha : d16059 q = 1) (hb : d277740 q = 1) : d278012 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16059, d278012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16059, d278012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16060 q = 1) (hb : d277740 q = 1) : d278013 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16060, d278013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16060, d278013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128240 q = 1) (hb : d277740 q = 1) : d278103 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128240, d278103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69661 q ha hb
    | true =>
      simp only [d128240, d278103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69668 q ha hb
  have h7 (q : Pattern) (ha : d16144 q = 1) (hb : d277740 q = 1) : d278116 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16144, d278116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69645 q ha hb
    | true =>
      simp only [d16144, d278116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69635 q ha hb
  have h8 (q : Pattern) (ha : d128241 q = 1) (hb : d277740 q = 1) : d278117 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128241, d278117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128241, d278117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128242 q = 1) (hb : d277740 q = 1) : d278118 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128242, d278118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128242, d278118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128243 q = 1) (hb : d277740 q = 1) : d278119 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128243, d278119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128243, d278119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128247 q = 1) (hb : d277740 q = 1) : d278123 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128247, d278123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128247, d278123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69669 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d277740 q = 1) : d278125 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d278125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, d278125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69636 q ha hb
  have h13 (q : Pattern) (ha : d128248 q = 1) (hb : d277740 q = 1) : d278126 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128248, d278126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128248, d278126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128249 q = 1) (hb : d277740 q = 1) : d278127 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128249, d278127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128249, d278127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128250 q = 1) (hb : d277740 q = 1) : d278128 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128250, d278128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128250, d278128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128251 q = 1) (hb : d277740 q = 1) : d278129 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128251, d278129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128251, d278129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128257 q = 1) (hb : d277740 q = 1) : d278186 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128257, d278186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128257, d278186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69677 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d277740 q = 1) : d278197 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, d278197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, d278197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69639 q ha hb
  have h19 (q : Pattern) (ha : d128258 q = 1) (hb : d277740 q = 1) : d278198 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128258, d278198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128258, d278198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128259 q = 1) (hb : d277740 q = 1) : d278199 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128259, d278199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128259, d278199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128260 q = 1) (hb : d277740 q = 1) : d278200 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128260, d278200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128260, d278200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128261 q = 1) (hb : d277740 q = 1) : d278201 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128261, d278201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128261, d278201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128262 q = 1) (hb : d277740 q = 1) : d278202 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128262, d278202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128262, d278202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro69679 (p : Pattern) (ha : d128268 p = 1) (hb : d277740 p = 1) : d278208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128263 q = 1) (hb : d277740 q = 1) : d278203 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128263, d278203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128263, d278203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69678 q ha hb
  have h2 (q : Pattern) (ha : d128264 q = 1) (hb : d277740 q = 1) : d278204 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128264, d278204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128264, d278204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128265 q = 1) (hb : d277740 q = 1) : d278205 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128265, d278205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128265, d278205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128266 q = 1) (hb : d277740 q = 1) : d278206 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128266, d278206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128266, d278206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128267 q = 1) (hb : d277740 q = 1) : d278207 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128267, d278207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128267, d278207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128268 q = 1) (hb : d277740 q = 1) : d278208 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128268, d278208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128268, d278208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69680 (p : Pattern) (ha : d750 p = 1) (hb : d277740 p = 1) : d278210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d133 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69592 q ha hb
    | true =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d134 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d20 q = 1) (hb : d277740 q = 1) : d20 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d135 q = 1) (hb : d277740 q = 1) : d277744 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d135, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d21 q = 1) (hb : d277740 q = 1) : d21 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d136 q = 1) (hb : d277740 q = 1) : d277745 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d136, d277745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d136, d277745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d137 q = 1) (hb : d277740 q = 1) : d277746 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d137, d277746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d137, d277746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d750 q = 1) (hb : d277740 q = 1) : d278210 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d750, d278210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d750, d278210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h10 p ha hb
theorem andIntro69681 (p : Pattern) (ha : d758 p = 1) (hb : d277740 p = 1) : d278219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d319 q = 1) (hb : d277740 q = 1) : d277860 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d277860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69613 q ha hb
    | true =>
      simp only [d319, d277860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d320 q = 1) (hb : d277740 q = 1) : d277861 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d277861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d320, d277861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d321 q = 1) (hb : d277740 q = 1) : d277862 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d321, d277862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d321, d277862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d322 q = 1) (hb : d277740 q = 1) : d277863 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d322, d277863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d322, d277863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d277740 q = 1) : d278211 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d278211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69680 q ha hb
    | true =>
      simp only [d751, d278211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d277740 q = 1) : d278212 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d278212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d278212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d277740 q = 1) : d278213 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d278213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d278213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d277740 q = 1) : d278214 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d278214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d278214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d755 q = 1) (hb : d277740 q = 1) : d278217 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d755, d278217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d755, d278217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d757 q = 1) (hb : d277740 q = 1) : d278218 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d278218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d757, d278218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d758 q = 1) (hb : d277740 q = 1) : d278219 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d758, d278219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d758, d278219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro69682 (p : Pattern) (ha : d762 p = 1) (hb : d277740 p = 1) : d278223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d751 q = 1) (hb : d277740 q = 1) : d278211 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d278211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69680 q ha hb
    | true =>
      simp only [d751, d278211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d752 q = 1) (hb : d277740 q = 1) : d278212 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d278212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d752, d278212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d753 q = 1) (hb : d277740 q = 1) : d278213 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d278213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d278213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d754 q = 1) (hb : d277740 q = 1) : d278214 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d278214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d754, d278214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d757 q = 1) (hb : d277740 q = 1) : d278218 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d278218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d757, d278218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d762 q = 1) (hb : d277740 q = 1) : d278223 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d762, d278223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d762, d278223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69683 (p : Pattern) (ha : d773 p = 1) (hb : d277740 p = 1) : d278234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d763 q = 1) (hb : d277740 q = 1) : d278224 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d278224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69681 q ha hb
    | true =>
      simp only [d763, d278224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69682 q ha hb
  have h2 (q : Pattern) (ha : d764 q = 1) (hb : d277740 q = 1) : d278225 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d278225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d278225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d765 q = 1) (hb : d277740 q = 1) : d278226 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d278226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d278226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d767 q = 1) (hb : d277740 q = 1) : d278228 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d278228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d767, d278228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d772 q = 1) (hb : d277740 q = 1) : d278233 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d278233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d772, d278233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d773 q = 1) (hb : d277740 q = 1) : d278234 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d773, d278234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d773, d278234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69684 (p : Pattern) (ha : d783 p = 1) (hb : d277740 p = 1) : d278244 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d277740 q = 1) : d278235 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69683 q ha hb
    | true =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d277740 q = 1) : d278236 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d277740 q = 1) : d278241 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d278241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d278241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d277740 q = 1) : d278242 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d278242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d278242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d277740 q = 1) : d278243 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d278243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d278243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d783 q = 1) (hb : d277740 q = 1) : d278244 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d783, d278244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d783, d278244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69685 (p : Pattern) (ha : d793 p = 1) (hb : d277740 p = 1) : d278254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d277740 q = 1) : d278235 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69683 q ha hb
    | true =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d277740 q = 1) : d278236 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d277740 q = 1) : d278241 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d278241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d278241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d277740 q = 1) : d278242 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d278242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d278242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d782 q = 1) (hb : d277740 q = 1) : d278243 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d782, d278243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d782, d278243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d793 q = 1) (hb : d277740 q = 1) : d278254 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d793, d278254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d793, d278254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69686 (p : Pattern) (ha : d950 p = 1) (hb : d277740 p = 1) : d278368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d939 q = 1) (hb : d277740 q = 1) : d278357 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d278357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69684 q ha hb
    | true =>
      simp only [d939, d278357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d940 q = 1) (hb : d277740 q = 1) : d278358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d278358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d278358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d941 q = 1) (hb : d277740 q = 1) : d278359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d278359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d941, d278359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d942 q = 1) (hb : d277740 q = 1) : d278360 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d278360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d278360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d943 q = 1) (hb : d277740 q = 1) : d278361 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d278361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d278361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d945 q = 1) (hb : d277740 q = 1) : d278363 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d278363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69685 q ha hb
    | true =>
      simp only [d945, d278363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d946 q = 1) (hb : d277740 q = 1) : d278364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d278364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d278364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d947 q = 1) (hb : d277740 q = 1) : d278365 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d278365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d947, d278365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d948 q = 1) (hb : d277740 q = 1) : d278366 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d278366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d278366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d949 q = 1) (hb : d277740 q = 1) : d278367 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d278367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d278367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d950 q = 1) (hb : d277740 q = 1) : d278368 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d950, d278368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d950, d278368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro69687 (p : Pattern) (ha : d959 p = 1) (hb : d277740 p = 1) : d278377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d945 q = 1) (hb : d277740 q = 1) : d278363 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d945, d278363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69685 q ha hb
    | true =>
      simp only [d945, d278363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d946 q = 1) (hb : d277740 q = 1) : d278364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d946, d278364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d946, d278364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d947 q = 1) (hb : d277740 q = 1) : d278365 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d947, d278365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d947, d278365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d948 q = 1) (hb : d277740 q = 1) : d278366 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d948, d278366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d948, d278366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d949 q = 1) (hb : d277740 q = 1) : d278367 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d949, d278367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d949, d278367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d959 q = 1) (hb : d277740 q = 1) : d278377 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d959, d278377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d959, d278377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69688 (p : Pattern) (ha : d981 p = 1) (hb : d277740 p = 1) : d278414 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d412 q = 1) (hb : d277740 q = 1) : d277931 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d277931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d277931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69613 q ha hb
  have h2 (q : Pattern) (ha : d319 q = 1) (hb : d277740 q = 1) : d277860 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d319, d277860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69613 q ha hb
    | true =>
      simp only [d319, d277860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d413 q = 1) (hb : d277740 q = 1) : d277932 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d413, d277932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d413, d277932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d320 q = 1) (hb : d277740 q = 1) : d277861 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d320, d277861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d320, d277861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d414 q = 1) (hb : d277740 q = 1) : d277933 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d414, d277933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d414, d277933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d415 q = 1) (hb : d277740 q = 1) : d277934 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d415, d277934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d415, d277934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d277740 q = 1) : d278398 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d278398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d278398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69680 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d277740 q = 1) : d278211 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d278211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69680 q ha hb
    | true =>
      simp only [d751, d278211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d277740 q = 1) : d278399 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d278399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d278399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d277740 q = 1) : d278212 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d278212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d278212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d277740 q = 1) : d278400 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d278400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d278400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d277740 q = 1) : d278401 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d278401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d278401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d975 q = 1) (hb : d277740 q = 1) : d278413 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d975, d278413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d975, d278413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d980 q = 1) (hb : d277740 q = 1) : d278407 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d278407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d980, d278407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d981 q = 1) (hb : d277740 q = 1) : d278414 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d981, d278414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d981, d278414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro69689 (p : Pattern) (ha : d986 p = 1) (hb : d277740 p = 1) : d278418 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d971 q = 1) (hb : d277740 q = 1) : d278398 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d278398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d278398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69680 q ha hb
  have h2 (q : Pattern) (ha : d751 q = 1) (hb : d277740 q = 1) : d278211 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d278211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69680 q ha hb
    | true =>
      simp only [d751, d278211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d972 q = 1) (hb : d277740 q = 1) : d278399 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d278399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d972, d278399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d752 q = 1) (hb : d277740 q = 1) : d278212 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d278212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d752, d278212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d973 q = 1) (hb : d277740 q = 1) : d278400 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d278400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d973, d278400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d974 q = 1) (hb : d277740 q = 1) : d278401 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d278401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d974, d278401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d980 q = 1) (hb : d277740 q = 1) : d278407 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d278407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d980, d278407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d986 q = 1) (hb : d277740 q = 1) : d278418 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d986, d278418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d986, d278418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro69690 (p : Pattern) (ha : d1005 p = 1) (hb : d277740 p = 1) : d278437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d987 q = 1) (hb : d277740 q = 1) : d278419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d278419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69688 q ha hb
    | true =>
      simp only [d987, d278419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69689 q ha hb
  have h2 (q : Pattern) (ha : d988 q = 1) (hb : d277740 q = 1) : d278420 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d278420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d278420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d989 q = 1) (hb : d277740 q = 1) : d278421 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d278421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d278421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d995 q = 1) (hb : d277740 q = 1) : d278427 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d278427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d995, d278427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1004 q = 1) (hb : d277740 q = 1) : d278436 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1004, d278436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1004, d278436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1005 q = 1) (hb : d277740 q = 1) : d278437 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1005, d278437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1005, d278437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69691 (p : Pattern) (ha : d1063 p = 1) (hb : d277740 p = 1) : d278460 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1006 q = 1) (hb : d277740 q = 1) : d278438 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d278438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69690 q ha hb
    | true =>
      simp only [d1006, d278438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1007 q = 1) (hb : d277740 q = 1) : d278439 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d278439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d278439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1060 q = 1) (hb : d277740 q = 1) : d278457 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1060, d278457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1060, d278457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1061 q = 1) (hb : d277740 q = 1) : d278458 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1061, d278458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1061, d278458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1062 q = 1) (hb : d277740 q = 1) : d278459 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1062, d278459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1062, d278459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1063 q = 1) (hb : d277740 q = 1) : d278460 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1063, d278460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1063, d278460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69692 (p : Pattern) (ha : d1069 p = 1) (hb : d277740 p = 1) : d278466 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1064 q = 1) (hb : d277740 q = 1) : d278461 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1064, d278461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69691 q ha hb
    | true =>
      simp only [d1064, d278461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1065 q = 1) (hb : d277740 q = 1) : d278462 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1065, d278462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1065, d278462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1066 q = 1) (hb : d277740 q = 1) : d278463 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1066, d278463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1066, d278463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1067 q = 1) (hb : d277740 q = 1) : d278464 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1067, d278464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1067, d278464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1068 q = 1) (hb : d277740 q = 1) : d278465 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1068, d278465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1068, d278465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1069 q = 1) (hb : d277740 q = 1) : d278466 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1069, d278466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1069, d278466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69693 (p : Pattern) (ha : d16227 p = 1) (hb : d277740 p = 1) : d278216 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d543 q = 1) (hb : d277740 q = 1) : d278035 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d278035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69652 q ha hb
    | true =>
      simp only [d543, d278035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d544 q = 1) (hb : d277740 q = 1) : d278036 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d278036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d544, d278036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d545 q = 1) (hb : d277740 q = 1) : d278037 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d545, d278037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d545, d278037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d546 q = 1) (hb : d277740 q = 1) : d278038 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d546, d278038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d546, d278038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9458 q = 1) (hb : d277740 q = 1) : d278040 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d278040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69654 q ha hb
    | true =>
      simp only [d9458, d278040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9460 q = 1) (hb : d277740 q = 1) : d278041 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d278041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9460, d278041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16073 q = 1) (hb : d277740 q = 1) : d278042 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16073, d278042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16073, d278042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16074 q = 1) (hb : d277740 q = 1) : d278043 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16074, d278043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16074, d278043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16075 q = 1) (hb : d277740 q = 1) : d278044 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16075, d278044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16075, d278044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9468 q = 1) (hb : d277740 q = 1) : d278048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d278048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69655 q ha hb
    | true =>
      simp only [d9468, d278048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9470 q = 1) (hb : d277740 q = 1) : d278049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d278049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9470, d278049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d12748 q = 1) (hb : d277740 q = 1) : d278050 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d278050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d278050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d12749 q = 1) (hb : d277740 q = 1) : d278051 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d278051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d12749, d278051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d751 q = 1) (hb : d277740 q = 1) : d278211 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d278211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69680 q ha hb
    | true =>
      simp only [d751, d278211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d752 q = 1) (hb : d277740 q = 1) : d278212 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d278212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d752, d278212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d753 q = 1) (hb : d277740 q = 1) : d278213 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d278213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d278213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d754 q = 1) (hb : d277740 q = 1) : d278214 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d278214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d754, d278214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12750 q = 1) (hb : d277740 q = 1) : d278215 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d278215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d12750, d278215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16227 q = 1) (hb : d277740 q = 1) : d278216 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16227, d278216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16227, d278216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro69694 (p : Pattern) (ha : d16233 p = 1) (hb : d277740 p = 1) : d278230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16228 q = 1) (hb : d277740 q = 1) : d278220 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d278220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69693 q ha hb
    | true =>
      simp only [d16228, d278220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69681 q ha hb
  have h2 (q : Pattern) (ha : d16229 q = 1) (hb : d277740 q = 1) : d278221 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16229, d278221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16229, d278221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16230 q = 1) (hb : d277740 q = 1) : d278222 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16230, d278222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16230, d278222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d763 q = 1) (hb : d277740 q = 1) : d278224 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d278224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69681 q ha hb
    | true =>
      simp only [d763, d278224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69682 q ha hb
  have h5 (q : Pattern) (ha : d764 q = 1) (hb : d277740 q = 1) : d278225 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d278225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d278225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d765 q = 1) (hb : d277740 q = 1) : d278226 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d278226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d278226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16231 q = 1) (hb : d277740 q = 1) : d278227 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16231, d278227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16231, d278227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d767 q = 1) (hb : d277740 q = 1) : d278228 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d278228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d767, d278228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16232 q = 1) (hb : d277740 q = 1) : d278229 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16232, d278229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16232, d278229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16233 q = 1) (hb : d277740 q = 1) : d278230 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16233, d278230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16233, d278230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro69695 (p : Pattern) (ha : d16239 p = 1) (hb : d277740 p = 1) : d278240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d277740 q = 1) : d278231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d278231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69694 q ha hb
    | true =>
      simp only [d16234, d278231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d277740 q = 1) : d278232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d278232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d278232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d277740 q = 1) : d278235 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69683 q ha hb
    | true =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d277740 q = 1) : d278236 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d277740 q = 1) : d278237 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d278237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d278237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d277740 q = 1) : d278238 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d278238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d278238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16238 q = 1) (hb : d277740 q = 1) : d278239 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16238, d278239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16238, d278239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16239 q = 1) (hb : d277740 q = 1) : d278240 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16239, d278240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16239, d278240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69696 (p : Pattern) (ha : d16245 p = 1) (hb : d277740 p = 1) : d278250 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d277740 q = 1) : d278245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d278245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69695 q ha hb
    | true =>
      simp only [d16240, d278245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69684 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d277740 q = 1) : d278246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d278246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d278246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d277740 q = 1) : d278247 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d278247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d278247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d277740 q = 1) : d278248 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d278248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d278248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d277740 q = 1) : d278249 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d278249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d278249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16245 q = 1) (hb : d277740 q = 1) : d278250 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16245, d278250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16245, d278250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69697 (p : Pattern) (ha : d16248 p = 1) (hb : d277740 p = 1) : d278253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d277740 q = 1) : d278231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d278231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69694 q ha hb
    | true =>
      simp only [d16234, d278231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d277740 q = 1) : d278232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d278232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d278232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d277740 q = 1) : d278235 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69683 q ha hb
    | true =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d277740 q = 1) : d278236 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d277740 q = 1) : d278237 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d278237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d278237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d277740 q = 1) : d278238 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d278238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d278238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16238 q = 1) (hb : d277740 q = 1) : d278239 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16238, d278239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16238, d278239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16248 q = 1) (hb : d277740 q = 1) : d278253 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16248, d278253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16248, d278253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro69698 (p : Pattern) (ha : d16254 p = 1) (hb : d277740 p = 1) : d278260 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d277740 q = 1) : d278245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d278245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69695 q ha hb
    | true =>
      simp only [d16240, d278245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69684 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d277740 q = 1) : d278246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d278246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d278246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d277740 q = 1) : d278247 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d278247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d278247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d277740 q = 1) : d278248 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d278248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d278248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d277740 q = 1) : d278249 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d278249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d278249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16249 q = 1) (hb : d277740 q = 1) : d278255 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16249, d278255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69697 q ha hb
    | true =>
      simp only [d16249, d278255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69685 q ha hb
  have h7 (q : Pattern) (ha : d16250 q = 1) (hb : d277740 q = 1) : d278256 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16250, d278256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16250, d278256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16251 q = 1) (hb : d277740 q = 1) : d278257 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16251, d278257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16251, d278257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16252 q = 1) (hb : d277740 q = 1) : d278258 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16252, d278258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16252, d278258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16253 q = 1) (hb : d277740 q = 1) : d278259 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16253, d278259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16253, d278259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16254 q = 1) (hb : d277740 q = 1) : d278260 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16254, d278260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16254, d278260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro69699 (p : Pattern) (ha : d16343 p = 1) (hb : d277740 p = 1) : d278362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16240 q = 1) (hb : d277740 q = 1) : d278245 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16240, d278245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69695 q ha hb
    | true =>
      simp only [d16240, d278245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69684 q ha hb
  have h2 (q : Pattern) (ha : d16241 q = 1) (hb : d277740 q = 1) : d278246 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16241, d278246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16241, d278246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16242 q = 1) (hb : d277740 q = 1) : d278247 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16242, d278247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16242, d278247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16243 q = 1) (hb : d277740 q = 1) : d278248 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16243, d278248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16243, d278248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16244 q = 1) (hb : d277740 q = 1) : d278249 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d16244, d278249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16244, d278249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d939 q = 1) (hb : d277740 q = 1) : d278357 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d278357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69684 q ha hb
    | true =>
      simp only [d939, d278357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d940 q = 1) (hb : d277740 q = 1) : d278358 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, d278358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, d278358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d941 q = 1) (hb : d277740 q = 1) : d278359 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, d278359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d941, d278359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d942 q = 1) (hb : d277740 q = 1) : d278360 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, d278360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, d278360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d943 q = 1) (hb : d277740 q = 1) : d278361 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, d278361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, d278361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16343 q = 1) (hb : d277740 q = 1) : d278362 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d16343, d278362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16343, d278362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro69700 (p : Pattern) (ha : d806 p = 1) (hb : d277740 p = 1) : d278267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d277740 q = 1) : d278235 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69683 q ha hb
    | true =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d277740 q = 1) : d278236 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d277740 q = 1) : d278241 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d278241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d278241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d277740 q = 1) : d278242 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d278242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d278242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d277740 q = 1) : d278266 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d278266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d278266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d806 q = 1) (hb : d277740 q = 1) : d278267 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d278267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d278267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69701 (p : Pattern) (ha : d816 p = 1) (hb : d277740 p = 1) : d278277 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d277740 q = 1) : d278235 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69683 q ha hb
    | true =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d277740 q = 1) : d278236 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d277740 q = 1) : d278241 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d278241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d278241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d277740 q = 1) : d278275 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d278275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d278275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d277740 q = 1) : d278276 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d278276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d278276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d277740 q = 1) : d278277 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d278277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d278277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69702 (p : Pattern) (ha : d16259 p = 1) (hb : d277740 p = 1) : d278265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d277740 q = 1) : d278231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d278231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69694 q ha hb
    | true =>
      simp only [d16234, d278231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d277740 q = 1) : d278232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d278232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d278232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d277740 q = 1) : d278235 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69683 q ha hb
    | true =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d277740 q = 1) : d278236 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d277740 q = 1) : d278237 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d278237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d278237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d277740 q = 1) : d278238 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d278238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d278238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16258 q = 1) (hb : d277740 q = 1) : d278264 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16258, d278264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16258, d278264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16259 q = 1) (hb : d277740 q = 1) : d278265 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16259, d278265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16259, d278265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69703 (p : Pattern) (ha : d16266 p = 1) (hb : d277740 p = 1) : d278274 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d277740 q = 1) : d278231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d278231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69694 q ha hb
    | true =>
      simp only [d16234, d278231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d277740 q = 1) : d278232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d278232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d278232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d277740 q = 1) : d278235 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69683 q ha hb
    | true =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d277740 q = 1) : d278236 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d277740 q = 1) : d278237 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d278237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d278237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16264 q = 1) (hb : d277740 q = 1) : d278272 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16264, d278272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16264, d278272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16265 q = 1) (hb : d277740 q = 1) : d278273 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16265, d278273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16265, d278273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16266 q = 1) (hb : d277740 q = 1) : d278274 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16266, d278274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16266, d278274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69704 (p : Pattern) (ha : d821 p = 1) (hb : d277739 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d528 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d820 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d820, d277739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d820, d277739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d309 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d528 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d528, d216468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d528, d216468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d310 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d529 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d529, d277739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d529, d277739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d821 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69705 (p : Pattern) (ha : d827 p = 1) (hb : d277739 p = 1) : d34352 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d309 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d528 q = 1) (hb : d216468 q = 1) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d528, d216468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d528, d216468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d825 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d826 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d826, d277739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d826, d277739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d1 q = 1) (hb : d309 q = 1) : d309 q = 1 := by
    exact hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d129 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d310 q = 1) (hb : d216468 q = 1) : d825 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d310, d216468, d825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d534 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d535 q = 1) (hb : d277739 q = 1) : d5121 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d535, d277739, d5121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d535, d277739, d5121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d827 q = 1) (hb : d277739 q = 1) : d34352 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d827, d34352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d827, d34352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro69706 (p : Pattern) (ha : d833 p = 1) (hb : d277740 p = 1) : d278283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d822 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69704 q ha hb
    | true =>
      simp only [d822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d823 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d277740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d823, d277740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d531 q = 1) (hb : d277739 q = 1) : d34353 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d34353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69650 q ha hb
    | true =>
      simp only [d531, d34353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d532 q = 1) (hb : d277740 q = 1) : d34354 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d277740, d34354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d532, d277740, d34354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d824 q = 1) (hb : d277740 q = 1) : d34355 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d824, d34355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d824, d34355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d828 q = 1) (hb : d277739 q = 1) : d34353 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d828, d34353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69705 q ha hb
    | true =>
      simp only [d828, d34353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d829 q = 1) (hb : d277740 q = 1) : d34354 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d829, d277740, d34354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d829, d277740, d34354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d537 q = 1) (hb : d277739 q = 1) : d277854 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69651 q ha hb
    | true =>
      simp only [d537, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d538 q = 1) (hb : d277740 q = 1) : d277855 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d538, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d830 q = 1) (hb : d277740 q = 1) : d278031 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d830, d278031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d830, d278031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d831 q = 1) (hb : d277740 q = 1) : d278281 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d831, d278281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d831, d278281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d832 q = 1) (hb : d277740 q = 1) : d278282 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d832, d278282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d832, d278282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d313 q = 1) (hb : d277739 q = 1) : d277854 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69612 q ha hb
    | true =>
      simp only [d313, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d314 q = 1) (hb : d277740 q = 1) : d277855 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d314, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d533 q = 1) (hb : d277740 q = 1) : d278031 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d278031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d533, d278031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d133 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69592 q ha hb
    | true =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d134 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h20 (q : Pattern) (ha : d539 q = 1) (hb : d277740 q = 1) : d277856 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d539, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d540 q = 1) (hb : d277740 q = 1) : d278032 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d540, d278032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d540, d278032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d541 q = 1) (hb : d277740 q = 1) : d278033 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d541, d278033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d541, d278033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h23 (q : Pattern) (ha : d833 q = 1) (hb : d277740 q = 1) : d278283 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d833, d278283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d833, d278283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro69707 (p : Pattern) (ha : d9580 p = 1) (hb : d277739 p = 1) : d5122 p = 1 := by
  have h0 (q : Pattern) (ha : d5121 q = 1) (hb : d277739 q = 1) : d5121 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1531 q = 1) (hb : d216468 q = 1) : d1531 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d16 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9579 q = 1) (hb : d277739 q = 1) : d1547 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d9579, d277739, d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9579, d277739, d1547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d9580 q = 1) (hb : d277739 q = 1) : d5122 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d9580, d5122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9580, d5122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h4 p ha hb
theorem andIntro69708 (p : Pattern) (ha : d9586 p = 1) (hb : d277740 p = 1) : d278291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d277739 q = 1) : d34353 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d34353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69650 q ha hb
    | true =>
      simp only [d531, d34353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d532 q = 1) (hb : d277740 q = 1) : d34354 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d277740, d34354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d277740, d34354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d313 q = 1) (hb : d277739 q = 1) : d277854 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d313, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69612 q ha hb
    | true =>
      simp only [d313, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d314 q = 1) (hb : d277740 q = 1) : d277855 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d314, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d314, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d533 q = 1) (hb : d277740 q = 1) : d278031 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d533, d278031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d533, d278031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d537 q = 1) (hb : d277739 q = 1) : d277854 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69651 q ha hb
    | true =>
      simp only [d537, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d538 q = 1) (hb : d277740 q = 1) : d277855 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d538, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d133 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69592 q ha hb
    | true =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d134 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d539 q = 1) (hb : d277740 q = 1) : d277856 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d539, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d540 q = 1) (hb : d277740 q = 1) : d278032 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d540, d278032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d540, d278032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d541 q = 1) (hb : d277740 q = 1) : d278033 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d541, d278033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d541, d278033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d9581 q = 1) (hb : d277739 q = 1) : d10057 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9581, d10057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69707 q ha hb
    | true =>
      simp only [d9581, d10057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d9582 q = 1) (hb : d277740 q = 1) : d10058 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d277740, d10058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9582, d277740, d10058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h17 (q : Pattern) (ha : d9452 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69653 q ha hb
    | true =>
      simp only [d9452, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d9453 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9453, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d9583 q = 1) (hb : d277740 q = 1) : d278288 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9583, d278288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9583, d278288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d9584 q = 1) (hb : d277740 q = 1) : d278289 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9584, d278289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9584, d278289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h21 (q : Pattern) (ha : d9585 q = 1) (hb : d277740 q = 1) : d278290 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9585, d278290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9585, d278290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h22 (q : Pattern) (ha : d9586 q = 1) (hb : d277740 q = 1) : d278291 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9586, d278291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9586, d278291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro69709 (p : Pattern) (ha : d9596 p = 1) (hb : d277740 p = 1) : d278300 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d531 q = 1) (hb : d277739 q = 1) : d34353 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d531, d34353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69650 q ha hb
    | true =>
      simp only [d531, d34353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d532 q = 1) (hb : d277740 q = 1) : d34354 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d532, d277740, d34354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d532, d277740, d34354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9581 q = 1) (hb : d277739 q = 1) : d10057 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9581, d10057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69707 q ha hb
    | true =>
      simp only [d9581, d10057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9582 q = 1) (hb : d277740 q = 1) : d10058 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d277740, d10058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9582, d277740, d10058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h6 (q : Pattern) (ha : d9593 q = 1) (hb : d277740 q = 1) : d278297 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9593, d278297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9593, d278297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d9594 q = 1) (hb : d277740 q = 1) : d278298 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9594, d278298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9594, d278298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d9595 q = 1) (hb : d277740 q = 1) : d278299 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9595, d278299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9595, d278299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d9452 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69653 q ha hb
    | true =>
      simp only [d9452, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9453 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9453, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d9583 q = 1) (hb : d277740 q = 1) : d278288 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9583, d278288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9583, d278288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9584 q = 1) (hb : d277740 q = 1) : d278289 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9584, d278289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9584, d278289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h14 (q : Pattern) (ha : d9585 q = 1) (hb : d277740 q = 1) : d278290 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9585, d278290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9585, d278290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d9596 q = 1) (hb : d277740 q = 1) : d278300 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9596, d278300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9596, d278300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro69710 (p : Pattern) (ha : d16274 p = 1) (hb : d277740 p = 1) : d278306 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d834 q = 1) (hb : d277740 q = 1) : d278284 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d278284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69706 q ha hb
    | true =>
      simp only [d834, d278284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d835 q = 1) (hb : d277740 q = 1) : d278285 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d278285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d835, d278285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d836 q = 1) (hb : d277740 q = 1) : d278286 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d836, d278286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d836, d278286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d837 q = 1) (hb : d277740 q = 1) : d278287 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d837, d278287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d837, d278287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9587 q = 1) (hb : d277740 q = 1) : d278292 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d278292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69708 q ha hb
    | true =>
      simp only [d9587, d278292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9589 q = 1) (hb : d277740 q = 1) : d278293 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9589, d278293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9589, d278293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16270 q = 1) (hb : d277740 q = 1) : d278294 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16270, d278294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16270, d278294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16271 q = 1) (hb : d277740 q = 1) : d278295 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16271, d278295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16271, d278295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16272 q = 1) (hb : d277740 q = 1) : d278296 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16272, d278296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16272, d278296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9597 q = 1) (hb : d277740 q = 1) : d278301 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d278301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69709 q ha hb
    | true =>
      simp only [d9597, d278301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9599 q = 1) (hb : d277740 q = 1) : d278302 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9599, d278302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9599, d278302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14529 q = 1) (hb : d277740 q = 1) : d278303 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14529, d278303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14529, d278303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14530 q = 1) (hb : d277740 q = 1) : d278304 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14530, d278304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14530, d278304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9468 q = 1) (hb : d277740 q = 1) : d278048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d278048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69655 q ha hb
    | true =>
      simp only [d9468, d278048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9470 q = 1) (hb : d277740 q = 1) : d278049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d278049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9470, d278049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12748 q = 1) (hb : d277740 q = 1) : d278050 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d278050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d278050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d12749 q = 1) (hb : d277740 q = 1) : d278051 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d278051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12749, d278051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16273 q = 1) (hb : d277740 q = 1) : d278305 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16273, d278305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16273, d278305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16274 q = 1) (hb : d277740 q = 1) : d278306 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16274, d278306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16274, d278306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro69711 (p : Pattern) (ha : d16278 p = 1) (hb : d277740 p = 1) : d278310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9468 q = 1) (hb : d277740 q = 1) : d278048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d278048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69655 q ha hb
    | true =>
      simp only [d9468, d278048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d9470 q = 1) (hb : d277740 q = 1) : d278049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d278049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9470, d278049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12748 q = 1) (hb : d277740 q = 1) : d278050 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12748, d278050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12748, d278050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d12749 q = 1) (hb : d277740 q = 1) : d278051 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12749, d278051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12749, d278051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d751 q = 1) (hb : d277740 q = 1) : d278211 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d278211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69680 q ha hb
    | true =>
      simp only [d751, d278211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d752 q = 1) (hb : d277740 q = 1) : d278212 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d278212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d752, d278212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d753 q = 1) (hb : d277740 q = 1) : d278213 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d753, d278213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d753, d278213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d754 q = 1) (hb : d277740 q = 1) : d278214 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d754, d278214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d754, d278214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d12750 q = 1) (hb : d277740 q = 1) : d278215 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12750, d278215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d12750, d278215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d757 q = 1) (hb : d277740 q = 1) : d278218 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d757, d278218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d757, d278218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16278 q = 1) (hb : d277740 q = 1) : d278310 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16278, d278310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16278, d278310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro69712 (p : Pattern) (ha : d16284 p = 1) (hb : d277740 p = 1) : d278316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16275 q = 1) (hb : d277740 q = 1) : d278307 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16275, d278307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69710 q ha hb
    | true =>
      simp only [d16275, d278307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69693 q ha hb
  have h2 (q : Pattern) (ha : d16276 q = 1) (hb : d277740 q = 1) : d278308 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16276, d278308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16276, d278308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16277 q = 1) (hb : d277740 q = 1) : d278309 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16277, d278309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16277, d278309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16279 q = 1) (hb : d277740 q = 1) : d278311 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16279, d278311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69693 q ha hb
    | true =>
      simp only [d16279, d278311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69711 q ha hb
  have h5 (q : Pattern) (ha : d16280 q = 1) (hb : d277740 q = 1) : d278312 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16280, d278312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16280, d278312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16281 q = 1) (hb : d277740 q = 1) : d278313 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16281, d278313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16281, d278313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16282 q = 1) (hb : d277740 q = 1) : d278314 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16282, d278314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16282, d278314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16228 q = 1) (hb : d277740 q = 1) : d278220 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d278220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69693 q ha hb
    | true =>
      simp only [d16228, d278220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69681 q ha hb
  have h9 (q : Pattern) (ha : d16229 q = 1) (hb : d277740 q = 1) : d278221 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16229, d278221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16229, d278221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16230 q = 1) (hb : d277740 q = 1) : d278222 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16230, d278222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16230, d278222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d763 q = 1) (hb : d277740 q = 1) : d278224 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d278224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69681 q ha hb
    | true =>
      simp only [d763, d278224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69682 q ha hb
  have h12 (q : Pattern) (ha : d764 q = 1) (hb : d277740 q = 1) : d278225 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d278225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d278225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d765 q = 1) (hb : d277740 q = 1) : d278226 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d278226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d278226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16231 q = 1) (hb : d277740 q = 1) : d278227 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16231, d278227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16231, d278227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16283 q = 1) (hb : d277740 q = 1) : d278315 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16283, d278315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16283, d278315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16284 q = 1) (hb : d277740 q = 1) : d278316 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16284, d278316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16284, d278316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro69713 (p : Pattern) (ha : d16290 p = 1) (hb : d277740 p = 1) : d278322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16285 q = 1) (hb : d277740 q = 1) : d278317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16285, d278317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69712 q ha hb
    | true =>
      simp only [d16285, d278317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16286 q = 1) (hb : d277740 q = 1) : d278318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16286, d278318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16286, d278318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16234 q = 1) (hb : d277740 q = 1) : d278231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d278231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69694 q ha hb
    | true =>
      simp only [d16234, d278231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16235 q = 1) (hb : d277740 q = 1) : d278232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d278232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d278232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16287 q = 1) (hb : d277740 q = 1) : d278319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16287, d278319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16287, d278319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16288 q = 1) (hb : d277740 q = 1) : d278320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16288, d278320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16288, d278320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16289 q = 1) (hb : d277740 q = 1) : d278321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16289, d278321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16289, d278321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16290 q = 1) (hb : d277740 q = 1) : d278322 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16290, d278322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16290, d278322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69714 (p : Pattern) (ha : d16314 p = 1) (hb : d277740 p = 1) : d278328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d277740 q = 1) : d278231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d278231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69694 q ha hb
    | true =>
      simp only [d16234, d278231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d277740 q = 1) : d278232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d278232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d278232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16311 q = 1) (hb : d277740 q = 1) : d278325 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16311, d278325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16311, d278325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16312 q = 1) (hb : d277740 q = 1) : d278326 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16312, d278326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16312, d278326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16313 q = 1) (hb : d277740 q = 1) : d278327 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16313, d278327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16313, d278327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16314 q = 1) (hb : d277740 q = 1) : d278328 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16314, d278328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16314, d278328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69715 (p : Pattern) (ha : d128274 p = 1) (hb : d277740 p = 1) : d278334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16260 q = 1) (hb : d277740 q = 1) : d278268 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16260, d278268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69702 q ha hb
    | true =>
      simp only [d16260, d278268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69700 q ha hb
  have h2 (q : Pattern) (ha : d16261 q = 1) (hb : d277740 q = 1) : d278269 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16261, d278269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16261, d278269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16262 q = 1) (hb : d277740 q = 1) : d278270 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16262, d278270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16262, d278270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16263 q = 1) (hb : d277740 q = 1) : d278271 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16263, d278271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16263, d278271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16267 q = 1) (hb : d277740 q = 1) : d278278 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16267, d278278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69703 q ha hb
    | true =>
      simp only [d16267, d278278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69701 q ha hb
  have h6 (q : Pattern) (ha : d16268 q = 1) (hb : d277740 q = 1) : d278279 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16268, d278279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16268, d278279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16269 q = 1) (hb : d277740 q = 1) : d278280 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16269, d278280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16269, d278280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16291 q = 1) (hb : d277740 q = 1) : d278323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16291, d278323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69713 q ha hb
    | true =>
      simp only [d16291, d278323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69695 q ha hb
  have h9 (q : Pattern) (ha : d128270 q = 1) (hb : d277740 q = 1) : d278324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128270, d278324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128270, d278324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16315 q = 1) (hb : d277740 q = 1) : d278329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16315, d278329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69714 q ha hb
    | true =>
      simp only [d16315, d278329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16316 q = 1) (hb : d277740 q = 1) : d278330 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16316, d278330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16316, d278330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128271 q = 1) (hb : d277740 q = 1) : d278331 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128271, d278331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128271, d278331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128272 q = 1) (hb : d277740 q = 1) : d278332 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128272, d278332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128272, d278332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128273 q = 1) (hb : d277740 q = 1) : d278333 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128273, d278333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128273, d278333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d128274 q = 1) (hb : d277740 q = 1) : d278334 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128274, d278334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128274, d278334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro69716 (p : Pattern) (ha : d916 p = 1) (hb : d277740 p = 1) : d278336 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d277740 q = 1) : d278235 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69683 q ha hb
    | true =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d277740 q = 1) : d278236 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d277740 q = 1) : d278241 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d278241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d278241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d277740 q = 1) : d278242 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d278242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d278242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d277740 q = 1) : d278266 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d278266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d278266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d916 q = 1) (hb : d277740 q = 1) : d278336 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, d278336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, d278336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69717 (p : Pattern) (ha : d922 p = 1) (hb : d277740 p = 1) : d278342 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d277740 q = 1) : d278235 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69683 q ha hb
    | true =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d277740 q = 1) : d278236 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d277740 q = 1) : d278241 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d278241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d278241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d277740 q = 1) : d278275 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d278275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d278275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d277740 q = 1) : d278276 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d278276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d278276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d277740 q = 1) : d278342 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, d278342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, d278342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69718 (p : Pattern) (ha : d16321 p = 1) (hb : d277740 p = 1) : d278335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d277740 q = 1) : d278231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d278231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69694 q ha hb
    | true =>
      simp only [d16234, d278231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d277740 q = 1) : d278232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d278232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d278232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d277740 q = 1) : d278235 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69683 q ha hb
    | true =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d277740 q = 1) : d278236 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d277740 q = 1) : d278237 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d278237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d278237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16237 q = 1) (hb : d277740 q = 1) : d278238 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16237, d278238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16237, d278238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16258 q = 1) (hb : d277740 q = 1) : d278264 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16258, d278264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16258, d278264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16321 q = 1) (hb : d277740 q = 1) : d278335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16321, d278335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16321, d278335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro69719 (p : Pattern) (ha : d16326 p = 1) (hb : d277740 p = 1) : d278341 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d277740 q = 1) : d278231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d278231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69694 q ha hb
    | true =>
      simp only [d16234, d278231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d277740 q = 1) : d278232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d278232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d278232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d277740 q = 1) : d278235 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69683 q ha hb
    | true =>
      simp only [d774, d278235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d277740 q = 1) : d278236 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d278236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16236 q = 1) (hb : d277740 q = 1) : d278237 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16236, d278237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16236, d278237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16264 q = 1) (hb : d277740 q = 1) : d278272 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16264, d278272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16264, d278272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16265 q = 1) (hb : d277740 q = 1) : d278273 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16265, d278273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16265, d278273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16326 q = 1) (hb : d277740 q = 1) : d278341 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16326, d278341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16326, d278341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro69720 (p : Pattern) (ha : d16330 p = 1) (hb : d277740 p = 1) : d278346 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16285 q = 1) (hb : d277740 q = 1) : d278317 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16285, d278317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69712 q ha hb
    | true =>
      simp only [d16285, d278317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16286 q = 1) (hb : d277740 q = 1) : d278318 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16286, d278318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16286, d278318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16234 q = 1) (hb : d277740 q = 1) : d278231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d278231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69694 q ha hb
    | true =>
      simp only [d16234, d278231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16235 q = 1) (hb : d277740 q = 1) : d278232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d278232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d278232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16287 q = 1) (hb : d277740 q = 1) : d278319 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16287, d278319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16287, d278319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16288 q = 1) (hb : d277740 q = 1) : d278320 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16288, d278320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16288, d278320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16289 q = 1) (hb : d277740 q = 1) : d278321 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16289, d278321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16289, d278321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16330 q = 1) (hb : d277740 q = 1) : d278346 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16330, d278346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16330, d278346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro69721 (p : Pattern) (ha : d16335 p = 1) (hb : d277740 p = 1) : d278349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16234 q = 1) (hb : d277740 q = 1) : d278231 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16234, d278231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69694 q ha hb
    | true =>
      simp only [d16234, d278231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16235 q = 1) (hb : d277740 q = 1) : d278232 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16235, d278232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16235, d278232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16311 q = 1) (hb : d277740 q = 1) : d278325 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16311, d278325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16311, d278325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16312 q = 1) (hb : d277740 q = 1) : d278326 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16312, d278326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16312, d278326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16313 q = 1) (hb : d277740 q = 1) : d278327 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16313, d278327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16313, d278327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16335 q = 1) (hb : d277740 q = 1) : d278349 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16335, d278349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16335, d278349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69722 (p : Pattern) (ha : d128279 p = 1) (hb : d277740 p = 1) : d278355 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16260 q = 1) (hb : d277740 q = 1) : d278268 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16260, d278268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69702 q ha hb
    | true =>
      simp only [d16260, d278268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69700 q ha hb
  have h2 (q : Pattern) (ha : d16261 q = 1) (hb : d277740 q = 1) : d278269 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16261, d278269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16261, d278269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16262 q = 1) (hb : d277740 q = 1) : d278270 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16262, d278270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16262, d278270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16263 q = 1) (hb : d277740 q = 1) : d278271 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16263, d278271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16263, d278271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16267 q = 1) (hb : d277740 q = 1) : d278278 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16267, d278278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69703 q ha hb
    | true =>
      simp only [d16267, d278278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69701 q ha hb
  have h6 (q : Pattern) (ha : d16268 q = 1) (hb : d277740 q = 1) : d278279 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16268, d278279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16268, d278279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16269 q = 1) (hb : d277740 q = 1) : d278280 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16269, d278280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16269, d278280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16291 q = 1) (hb : d277740 q = 1) : d278323 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16291, d278323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69713 q ha hb
    | true =>
      simp only [d16291, d278323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69695 q ha hb
  have h9 (q : Pattern) (ha : d128270 q = 1) (hb : d277740 q = 1) : d278324 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128270, d278324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128270, d278324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d16315 q = 1) (hb : d277740 q = 1) : d278329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16315, d278329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69714 q ha hb
    | true =>
      simp only [d16315, d278329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16316 q = 1) (hb : d277740 q = 1) : d278330 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16316, d278330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16316, d278330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128271 q = 1) (hb : d277740 q = 1) : d278331 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128271, d278331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d128271, d278331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d128272 q = 1) (hb : d277740 q = 1) : d278332 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128272, d278332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d128272, d278332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128273 q = 1) (hb : d277740 q = 1) : d278333 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128273, d278333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d128273, d278333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16322 q = 1) (hb : d277740 q = 1) : d278337 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16322, d278337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69718 q ha hb
    | true =>
      simp only [d16322, d278337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69716 q ha hb
  have h16 (q : Pattern) (ha : d16323 q = 1) (hb : d277740 q = 1) : d278338 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16323, d278338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16323, d278338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d16324 q = 1) (hb : d277740 q = 1) : d278339 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16324, d278339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d16324, d278339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16325 q = 1) (hb : d277740 q = 1) : d278340 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d16325, d278340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16325, d278340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16327 q = 1) (hb : d277740 q = 1) : d278343 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16327, d278343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69719 q ha hb
    | true =>
      simp only [d16327, d278343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69717 q ha hb
  have h20 (q : Pattern) (ha : d16328 q = 1) (hb : d277740 q = 1) : d278344 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16328, d278344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16328, d278344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d16329 q = 1) (hb : d277740 q = 1) : d278345 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d16329, d278345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d16329, d278345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d16331 q = 1) (hb : d277740 q = 1) : d278347 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16331, d278347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69720 q ha hb
    | true =>
      simp only [d16331, d278347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69697 q ha hb
  have h23 (q : Pattern) (ha : d128275 q = 1) (hb : d277740 q = 1) : d278348 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128275, d278348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d128275, d278348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d16336 q = 1) (hb : d277740 q = 1) : d278350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16336, d278350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69721 q ha hb
    | true =>
      simp only [d16336, d278350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d16337 q = 1) (hb : d277740 q = 1) : d278351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16337, d278351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d16337, d278351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d128276 q = 1) (hb : d277740 q = 1) : d278352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128276, d278352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d128276, d278352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d128277 q = 1) (hb : d277740 q = 1) : d278353 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128277, d278353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128277, d278353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d128278 q = 1) (hb : d277740 q = 1) : d278354 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128278, d278354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d128278, d278354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d128279 q = 1) (hb : d277740 q = 1) : d278355 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128279, d278355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128279, d278355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro69723 (p : Pattern) (ha : d128286 p = 1) (hb : d277740 p = 1) : d278375 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16331 q = 1) (hb : d277740 q = 1) : d278347 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16331, d278347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69720 q ha hb
    | true =>
      simp only [d16331, d278347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69697 q ha hb
  have h2 (q : Pattern) (ha : d128275 q = 1) (hb : d277740 q = 1) : d278348 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128275, d278348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128275, d278348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16336 q = 1) (hb : d277740 q = 1) : d278350 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16336, d278350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69721 q ha hb
    | true =>
      simp only [d16336, d278350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16337 q = 1) (hb : d277740 q = 1) : d278351 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16337, d278351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16337, d278351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128276 q = 1) (hb : d277740 q = 1) : d278352 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128276, d278352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128276, d278352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128284 q = 1) (hb : d277740 q = 1) : d278373 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128284, d278373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128284, d278373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128285 q = 1) (hb : d277740 q = 1) : d278374 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128285, d278374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128285, d278374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128286 q = 1) (hb : d277740 q = 1) : d278375 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128286, d278375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128286, d278375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69724 (p : Pattern) (ha : d16362 p = 1) (hb : d277740 p = 1) : d278397 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d965 q = 1) (hb : d277740 q = 1) : d278383 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d965, d278383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d965, d278383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69706 q ha hb
  have h2 (q : Pattern) (ha : d834 q = 1) (hb : d277740 q = 1) : d278284 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d834, d278284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69706 q ha hb
    | true =>
      simp only [d834, d278284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d966 q = 1) (hb : d277740 q = 1) : d278384 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d966, d278384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d966, d278384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d835 q = 1) (hb : d277740 q = 1) : d278285 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d835, d278285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d835, d278285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d967 q = 1) (hb : d277740 q = 1) : d278385 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d967, d278385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d967, d278385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d968 q = 1) (hb : d277740 q = 1) : d278386 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d968, d278386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d968, d278386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16356 q = 1) (hb : d277740 q = 1) : d278387 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16356, d278387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16356, d278387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69708 q ha hb
  have h8 (q : Pattern) (ha : d9587 q = 1) (hb : d277740 q = 1) : d278292 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9587, d278292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69708 q ha hb
    | true =>
      simp only [d9587, d278292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16357 q = 1) (hb : d277740 q = 1) : d278388 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16357, d278388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16357, d278388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9589 q = 1) (hb : d277740 q = 1) : d278293 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9589, d278293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9589, d278293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16358 q = 1) (hb : d277740 q = 1) : d278389 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16358, d278389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16358, d278389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16359 q = 1) (hb : d277740 q = 1) : d278390 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16359, d278390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16359, d278390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16360 q = 1) (hb : d277740 q = 1) : d278391 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16360, d278391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16360, d278391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d14644 q = 1) (hb : d277740 q = 1) : d278392 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14644, d278392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14644, d278392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69709 q ha hb
  have h15 (q : Pattern) (ha : d9597 q = 1) (hb : d277740 q = 1) : d278301 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9597, d278301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69709 q ha hb
    | true =>
      simp only [d9597, d278301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d14645 q = 1) (hb : d277740 q = 1) : d278393 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d14645, d278393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d14645, d278393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9599 q = 1) (hb : d277740 q = 1) : d278302 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9599, d278302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9599, d278302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d14646 q = 1) (hb : d277740 q = 1) : d278394 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14646, d278394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14646, d278394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d14647 q = 1) (hb : d277740 q = 1) : d278395 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14647, d278395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d14647, d278395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d12858 q = 1) (hb : d277740 q = 1) : d278139 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d278139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d278139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69655 q ha hb
  have h21 (q : Pattern) (ha : d9468 q = 1) (hb : d277740 q = 1) : d278048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d278048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69655 q ha hb
    | true =>
      simp only [d9468, d278048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d12859 q = 1) (hb : d277740 q = 1) : d278140 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d278140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d12859, d278140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9470 q = 1) (hb : d277740 q = 1) : d278049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d278049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d9470, d278049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d12860 q = 1) (hb : d277740 q = 1) : d278141 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d278141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d12860, d278141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d12861 q = 1) (hb : d277740 q = 1) : d278142 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d278142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d12861, d278142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d16361 q = 1) (hb : d277740 q = 1) : d278396 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16361, d278396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d16361, d278396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d16362 q = 1) (hb : d277740 q = 1) : d278397 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16362, d278397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16362, d278397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro69725 (p : Pattern) (ha : d16363 p = 1) (hb : d277740 p = 1) : d278403 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d659 q = 1) (hb : d277740 q = 1) : d278130 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d278130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d278130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69652 q ha hb
  have h2 (q : Pattern) (ha : d543 q = 1) (hb : d277740 q = 1) : d278035 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d543, d278035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69652 q ha hb
    | true =>
      simp only [d543, d278035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d660 q = 1) (hb : d277740 q = 1) : d278131 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d660, d278131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d660, d278131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d544 q = 1) (hb : d277740 q = 1) : d278036 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d544, d278036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d544, d278036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d661 q = 1) (hb : d277740 q = 1) : d278132 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d661, d278132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d661, d278132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d662 q = 1) (hb : d277740 q = 1) : d278133 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d662, d278133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d662, d278133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16156 q = 1) (hb : d277740 q = 1) : d278134 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d278134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16156, d278134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69654 q ha hb
  have h8 (q : Pattern) (ha : d9458 q = 1) (hb : d277740 q = 1) : d278040 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9458, d278040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69654 q ha hb
    | true =>
      simp only [d9458, d278040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16157 q = 1) (hb : d277740 q = 1) : d278135 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d16157, d278135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16157, d278135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9460 q = 1) (hb : d277740 q = 1) : d278041 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9460, d278041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d9460, d278041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d16158 q = 1) (hb : d277740 q = 1) : d278136 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16158, d278136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16158, d278136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d16159 q = 1) (hb : d277740 q = 1) : d278137 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16159, d278137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d16159, d278137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d16160 q = 1) (hb : d277740 q = 1) : d278138 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16160, d278138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16160, d278138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d12858 q = 1) (hb : d277740 q = 1) : d278139 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d278139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d278139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69655 q ha hb
  have h15 (q : Pattern) (ha : d9468 q = 1) (hb : d277740 q = 1) : d278048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d278048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69655 q ha hb
    | true =>
      simp only [d9468, d278048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d12859 q = 1) (hb : d277740 q = 1) : d278140 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d278140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d12859, d278140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9470 q = 1) (hb : d277740 q = 1) : d278049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d278049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d9470, d278049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d12860 q = 1) (hb : d277740 q = 1) : d278141 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d278141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d12860, d278141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d12861 q = 1) (hb : d277740 q = 1) : d278142 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d278142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d12861, d278142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d971 q = 1) (hb : d277740 q = 1) : d278398 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d278398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d278398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69680 q ha hb
  have h21 (q : Pattern) (ha : d751 q = 1) (hb : d277740 q = 1) : d278211 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d278211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69680 q ha hb
    | true =>
      simp only [d751, d278211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d972 q = 1) (hb : d277740 q = 1) : d278399 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d278399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d972, d278399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d752 q = 1) (hb : d277740 q = 1) : d278212 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d278212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d752, d278212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d973 q = 1) (hb : d277740 q = 1) : d278400 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d278400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d973, d278400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d974 q = 1) (hb : d277740 q = 1) : d278401 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d278401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d974, d278401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d12862 q = 1) (hb : d277740 q = 1) : d278402 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d278402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d12862, d278402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d16363 q = 1) (hb : d277740 q = 1) : d278403 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16363, d278403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16363, d278403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  exact h27 p ha hb
theorem andIntro69726 (p : Pattern) (ha : d16367 p = 1) (hb : d277740 p = 1) : d278408 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12858 q = 1) (hb : d277740 q = 1) : d278139 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d278139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d278139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69655 q ha hb
  have h2 (q : Pattern) (ha : d9468 q = 1) (hb : d277740 q = 1) : d278048 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9468, d278048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69655 q ha hb
    | true =>
      simp only [d9468, d278048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d12859 q = 1) (hb : d277740 q = 1) : d278140 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d12859, d278140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12859, d278140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d9470 q = 1) (hb : d277740 q = 1) : d278049 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9470, d278049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9470, d278049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d12860 q = 1) (hb : d277740 q = 1) : d278141 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d12860, d278141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d12860, d278141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d12861 q = 1) (hb : d277740 q = 1) : d278142 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d12861, d278142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d12861, d278142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d971 q = 1) (hb : d277740 q = 1) : d278398 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d278398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d278398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69680 q ha hb
  have h8 (q : Pattern) (ha : d751 q = 1) (hb : d277740 q = 1) : d278211 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d751, d278211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69680 q ha hb
    | true =>
      simp only [d751, d278211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d972 q = 1) (hb : d277740 q = 1) : d278399 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d972, d278399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d972, d278399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d752 q = 1) (hb : d277740 q = 1) : d278212 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d752, d278212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d752, d278212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d973 q = 1) (hb : d277740 q = 1) : d278400 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d973, d278400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d973, d278400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d974 q = 1) (hb : d277740 q = 1) : d278401 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d974, d278401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d974, d278401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d12862 q = 1) (hb : d277740 q = 1) : d278402 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d12862, d278402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d12862, d278402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d980 q = 1) (hb : d277740 q = 1) : d278407 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d980, d278407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d980, d278407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d16367 q = 1) (hb : d277740 q = 1) : d278408 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16367, d278408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16367, d278408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro69727 (p : Pattern) (ha : d16377 p = 1) (hb : d277740 p = 1) : d278424 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16364 q = 1) (hb : d277740 q = 1) : d278404 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16364, d278404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69724 q ha hb
    | true =>
      simp only [d16364, d278404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69725 q ha hb
  have h2 (q : Pattern) (ha : d16365 q = 1) (hb : d277740 q = 1) : d278405 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16365, d278405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16365, d278405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16366 q = 1) (hb : d277740 q = 1) : d278406 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16366, d278406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16366, d278406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16368 q = 1) (hb : d277740 q = 1) : d278409 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16368, d278409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69725 q ha hb
    | true =>
      simp only [d16368, d278409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69726 q ha hb
  have h5 (q : Pattern) (ha : d16369 q = 1) (hb : d277740 q = 1) : d278410 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16369, d278410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16369, d278410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16370 q = 1) (hb : d277740 q = 1) : d278411 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16370, d278411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16370, d278411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16371 q = 1) (hb : d277740 q = 1) : d278412 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16371, d278412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16371, d278412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16372 q = 1) (hb : d277740 q = 1) : d278415 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d278415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69725 q ha hb
    | true =>
      simp only [d16372, d278415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69688 q ha hb
  have h9 (q : Pattern) (ha : d16373 q = 1) (hb : d277740 q = 1) : d278416 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d278416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16373, d278416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16374 q = 1) (hb : d277740 q = 1) : d278417 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d278417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, d278417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d987 q = 1) (hb : d277740 q = 1) : d278419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d278419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69688 q ha hb
    | true =>
      simp only [d987, d278419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69689 q ha hb
  have h12 (q : Pattern) (ha : d988 q = 1) (hb : d277740 q = 1) : d278420 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d278420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d278420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d989 q = 1) (hb : d277740 q = 1) : d278421 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d278421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d278421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16375 q = 1) (hb : d277740 q = 1) : d278422 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d278422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16375, d278422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16376 q = 1) (hb : d277740 q = 1) : d278423 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16376, d278423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16376, d278423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d16377 q = 1) (hb : d277740 q = 1) : d278424 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16377, d278424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d16377, d278424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro69728 (p : Pattern) (ha : d16381 p = 1) (hb : d277740 p = 1) : d278429 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16372 q = 1) (hb : d277740 q = 1) : d278415 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16372, d278415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69725 q ha hb
    | true =>
      simp only [d16372, d278415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69688 q ha hb
  have h2 (q : Pattern) (ha : d16373 q = 1) (hb : d277740 q = 1) : d278416 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16373, d278416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16373, d278416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16374 q = 1) (hb : d277740 q = 1) : d278417 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16374, d278417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16374, d278417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d987 q = 1) (hb : d277740 q = 1) : d278419 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d278419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69688 q ha hb
    | true =>
      simp only [d987, d278419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69689 q ha hb
  have h5 (q : Pattern) (ha : d988 q = 1) (hb : d277740 q = 1) : d278420 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d278420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d278420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d989 q = 1) (hb : d277740 q = 1) : d278421 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d278421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d278421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16375 q = 1) (hb : d277740 q = 1) : d278422 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16375, d278422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16375, d278422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d995 q = 1) (hb : d277740 q = 1) : d278427 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d278427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d995, d278427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16380 q = 1) (hb : d277740 q = 1) : d278428 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16380, d278428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16380, d278428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16381 q = 1) (hb : d277740 q = 1) : d278429 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16381, d278429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16381, d278429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro69729 (p : Pattern) (ha : d16387 p = 1) (hb : d277740 p = 1) : d278435 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16378 q = 1) (hb : d277740 q = 1) : d278425 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16378, d278425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69727 q ha hb
    | true =>
      simp only [d16378, d278425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16379 q = 1) (hb : d277740 q = 1) : d278426 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16379, d278426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16379, d278426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16382 q = 1) (hb : d277740 q = 1) : d278430 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d278430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69728 q ha hb
    | true =>
      simp only [d16382, d278430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16383 q = 1) (hb : d277740 q = 1) : d278431 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d278431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d278431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16384 q = 1) (hb : d277740 q = 1) : d278432 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16384, d278432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16384, d278432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16385 q = 1) (hb : d277740 q = 1) : d278433 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16385, d278433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16385, d278433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16386 q = 1) (hb : d277740 q = 1) : d278434 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16386, d278434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16386, d278434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16387 q = 1) (hb : d277740 q = 1) : d278435 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16387, d278435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16387, d278435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro69730 (p : Pattern) (ha : d16391 p = 1) (hb : d277740 p = 1) : d278443 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16382 q = 1) (hb : d277740 q = 1) : d278430 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d278430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69728 q ha hb
    | true =>
      simp only [d16382, d278430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16383 q = 1) (hb : d277740 q = 1) : d278431 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d278431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d278431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d277740 q = 1) : d278438 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d278438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69690 q ha hb
    | true =>
      simp only [d1006, d278438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d277740 q = 1) : d278439 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d278439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d278439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16388 q = 1) (hb : d277740 q = 1) : d278440 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16388, d278440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16388, d278440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16389 q = 1) (hb : d277740 q = 1) : d278441 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16389, d278441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16389, d278441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16390 q = 1) (hb : d277740 q = 1) : d278442 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16390, d278442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16390, d278442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16391 q = 1) (hb : d277740 q = 1) : d278443 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16391, d278443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16391, d278443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro69731 (p : Pattern) (ha : d16417 p = 1) (hb : d277740 p = 1) : d278449 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16382 q = 1) (hb : d277740 q = 1) : d278430 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16382, d278430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69728 q ha hb
    | true =>
      simp only [d16382, d278430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16383 q = 1) (hb : d277740 q = 1) : d278431 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16383, d278431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16383, d278431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16414 q = 1) (hb : d277740 q = 1) : d278446 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16414, d278446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16414, d278446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16415 q = 1) (hb : d277740 q = 1) : d278447 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16415, d278447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16415, d278447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16416 q = 1) (hb : d277740 q = 1) : d278448 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16416, d278448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16416, d278448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16417 q = 1) (hb : d277740 q = 1) : d278449 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16417, d278449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16417, d278449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69732 (p : Pattern) (ha : d128296 p = 1) (hb : d277740 p = 1) : d278455 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16392 q = 1) (hb : d277740 q = 1) : d278444 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16392, d278444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69729 q ha hb
    | true =>
      simp only [d16392, d278444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69730 q ha hb
  have h2 (q : Pattern) (ha : d128292 q = 1) (hb : d277740 q = 1) : d278445 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d128292, d278445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d128292, d278445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16418 q = 1) (hb : d277740 q = 1) : d278450 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d16418, d278450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69731 q ha hb
    | true =>
      simp only [d16418, d278450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16419 q = 1) (hb : d277740 q = 1) : d278451 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d16419, d278451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16419, d278451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d128293 q = 1) (hb : d277740 q = 1) : d278452 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d128293, d278452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d128293, d278452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128294 q = 1) (hb : d277740 q = 1) : d278453 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d128294, d278453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128294, d278453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d128295 q = 1) (hb : d277740 q = 1) : d278454 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d128295, d278454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128295, d278454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d128296 q = 1) (hb : d277740 q = 1) : d278455 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d128296, d278455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128296, d278455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69733 (p : Pattern) (ha : d128302 p = 1) (hb : d277740 p = 1) : d278472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16246 q = 1) (hb : d277740 q = 1) : d278251 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16246, d278251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16246, d278251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69696 q ha hb
  have h2 (q : Pattern) (ha : d16247 q = 1) (hb : d277740 q = 1) : d278252 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16247, d278252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d16247, d278252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16255 q = 1) (hb : d277740 q = 1) : d278261 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16255, d278261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69696 q ha hb
    | true =>
      simp only [d16255, d278261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69698 q ha hb
  have h4 (q : Pattern) (ha : d16256 q = 1) (hb : d277740 q = 1) : d278262 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d16256, d278262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16256, d278262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16257 q = 1) (hb : d277740 q = 1) : d278263 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d16257, d278263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16257, d278263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128280 q = 1) (hb : d277740 q = 1) : d278356 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128280, d278356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69715 q ha hb
    | true =>
      simp only [d128280, d278356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69722 q ha hb
  have h7 (q : Pattern) (ha : d16344 q = 1) (hb : d277740 q = 1) : d278369 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d16344, d278369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69699 q ha hb
    | true =>
      simp only [d16344, d278369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69686 q ha hb
  have h8 (q : Pattern) (ha : d128281 q = 1) (hb : d277740 q = 1) : d278370 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128281, d278370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d128281, d278370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d128282 q = 1) (hb : d277740 q = 1) : d278371 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128282, d278371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d128282, d278371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d128283 q = 1) (hb : d277740 q = 1) : d278372 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128283, d278372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d128283, d278372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d128287 q = 1) (hb : d277740 q = 1) : d278376 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128287, d278376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128287, d278376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69723 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d277740 q = 1) : d278378 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d278378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d278378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69687 q ha hb
  have h13 (q : Pattern) (ha : d128288 q = 1) (hb : d277740 q = 1) : d278379 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128288, d278379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d128288, d278379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d128289 q = 1) (hb : d277740 q = 1) : d278380 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128289, d278380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d128289, d278380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d128290 q = 1) (hb : d277740 q = 1) : d278381 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128290, d278381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d128290, d278381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d128291 q = 1) (hb : d277740 q = 1) : d278382 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128291, d278382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d128291, d278382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d128297 q = 1) (hb : d277740 q = 1) : d278456 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d128297, d278456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128297, d278456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69732 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d277740 q = 1) : d278467 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d278467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d278467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69692 q ha hb
  have h19 (q : Pattern) (ha : d128298 q = 1) (hb : d277740 q = 1) : d278468 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d128298, d278468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d128298, d278468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d128299 q = 1) (hb : d277740 q = 1) : d278469 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d128299, d278469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d128299, d278469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d128300 q = 1) (hb : d277740 q = 1) : d278470 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d128300, d278470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d128300, d278470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d128301 q = 1) (hb : d277740 q = 1) : d278471 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d128301, d278471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d128301, d278471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d128302 q = 1) (hb : d277740 q = 1) : d278472 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d128302, d278472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d128302, d278472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro69734 (p : Pattern) (ha : d128308 p = 1) (hb : d277740 p = 1) : d278478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d128303 q = 1) (hb : d277740 q = 1) : d278473 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d128303, d278473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128303, d278473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69733 q ha hb
  have h2 (q : Pattern) (ha : d128304 q = 1) (hb : d277740 q = 1) : d278474 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d128304, d278474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128304, d278474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d128305 q = 1) (hb : d277740 q = 1) : d278475 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d128305, d278475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128305, d278475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d128306 q = 1) (hb : d277740 q = 1) : d278476 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d128306, d278476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128306, d278476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d128307 q = 1) (hb : d277740 q = 1) : d278477 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d128307, d278477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128307, d278477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d128308 q = 1) (hb : d277740 q = 1) : d278478 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d128308, d278478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d128308, d278478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro69735 (p : Pattern) (ha : d5017 p = 1) (hb : d277740 p = 1) : d278536 p = 1 := by
  have h0 (q : Pattern) (ha : d1093 q = 1) (hb : d277739 q = 1) : d1093 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1094 q = 1) (hb : d277739 q = 1) : d278486 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d278486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69612 q ha hb
    | true =>
      simp only [d1094, d278486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1095 q = 1) (hb : d277740 q = 1) : d278487 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d277740, d278487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1095, d277740, d278487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18 q = 1) (hb : d277739 q = 1) : d18 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d5012 q = 1) (hb : d277739 q = 1) : d278526 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5012, d278526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69653 q ha hb
    | true =>
      simp only [d5012, d278526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d5013 q = 1) (hb : d277740 q = 1) : d278527 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5013, d277740, d278527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5013, d277740, d278527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d5014 q = 1) (hb : d277740 q = 1) : d278528 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5014, d278528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5014, d278528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d133 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69592 q ha hb
    | true =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d134 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d20 q = 1) (hb : d277740 q = 1) : d20 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d135 q = 1) (hb : d277740 q = 1) : d277744 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d135, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d5015 q = 1) (hb : d277740 q = 1) : d278529 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5015, d278529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5015, d278529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d5016 q = 1) (hb : d277740 q = 1) : d278530 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5016, d278530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d5016, d278530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1119 q = 1) (hb : d277740 q = 1) : d1119 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d5017 q = 1) (hb : d277740 q = 1) : d278536 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d5017, d278536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d5017, d278536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro69736 (p : Pattern) (ha : d14773 p = 1) (hb : d277740 p = 1) : d278548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5018 q = 1) (hb : d277740 q = 1) : d278537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d5018, d278537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69735 q ha hb
    | true =>
      simp only [d5018, d278537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5019 q = 1) (hb : d277740 q = 1) : d278538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d5019, d278538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5019, d278538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5020 q = 1) (hb : d277740 q = 1) : d278539 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d5020, d278539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5020, d278539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d5021 q = 1) (hb : d277740 q = 1) : d278540 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d5021, d278540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5021, d278540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5022 q = 1) (hb : d277740 q = 1) : d278547 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d5022, d278547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5022, d278547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14772 q = 1) (hb : d277740 q = 1) : d14772 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14773 q = 1) (hb : d277740 q = 1) : d278548 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14773, d278548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14773, d278548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro69737 (p : Pattern) (ha : d1120 p = 1) (hb : d277740 p = 1) : d278536 p = 1 := by
  have h0 (q : Pattern) (ha : d1093 q = 1) (hb : d277739 q = 1) : d1093 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1094 q = 1) (hb : d277739 q = 1) : d278486 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d278486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69612 q ha hb
    | true =>
      simp only [d1094, d278486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1095 q = 1) (hb : d277740 q = 1) : d278487 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d277740, d278487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1095, d277740, d278487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18 q = 1) (hb : d277739 q = 1) : d18 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1104 q = 1) (hb : d277739 q = 1) : d278526 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1104, d278526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69592 q ha hb
    | true =>
      simp only [d1104, d278526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1105 q = 1) (hb : d277740 q = 1) : d278527 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1105, d277740, d278527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1105, d277740, d278527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d1106 q = 1) (hb : d277740 q = 1) : d278528 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1106, d278528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1106, d278528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d133 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69592 q ha hb
    | true =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d134 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d20 q = 1) (hb : d277740 q = 1) : d20 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d135 q = 1) (hb : d277740 q = 1) : d277744 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d135, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1107 q = 1) (hb : d277740 q = 1) : d278529 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1107, d278529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1107, d278529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1108 q = 1) (hb : d277740 q = 1) : d278530 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1108, d278530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1108, d278530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1119 q = 1) (hb : d277740 q = 1) : d1119 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d1120 q = 1) (hb : d277740 q = 1) : d278536 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1120, d278536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1120, d278536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro69738 (p : Pattern) (ha : d14778 p = 1) (hb : d277740 p = 1) : d278548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1121 q = 1) (hb : d277740 q = 1) : d278537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d278537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69737 q ha hb
    | true =>
      simp only [d1121, d278537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1122 q = 1) (hb : d277740 q = 1) : d278538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d278538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1122, d278538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1123 q = 1) (hb : d277740 q = 1) : d278539 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d278539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d278539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1124 q = 1) (hb : d277740 q = 1) : d278540 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d278540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1124, d278540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1127 q = 1) (hb : d277740 q = 1) : d278547 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1127, d278547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1127, d278547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d14772 q = 1) (hb : d277740 q = 1) : d14772 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d14778 q = 1) (hb : d277740 q = 1) : d278548 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d14778, d278548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d14778, d278548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro69739 (p : Pattern) (ha : d1099 p = 1) (hb : d277740 p = 1) : d278491 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d822 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69704 q ha hb
    | true =>
      simp only [d822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d823 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d277740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d823, d277740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1087 q = 1) (hb : d277739 q = 1) : d1087 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1088 q = 1) (hb : d277739 q = 1) : d278481 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d278481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69650 q ha hb
    | true =>
      simp only [d1088, d278481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1089 q = 1) (hb : d277740 q = 1) : d278482 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d277740, d278482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1089, d277740, d278482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d1090 q = 1) (hb : d277740 q = 1) : d278483 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1090, d278483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1090, d278483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d828 q = 1) (hb : d277739 q = 1) : d34353 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d828, d34353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69705 q ha hb
    | true =>
      simp only [d828, d34353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d829 q = 1) (hb : d277740 q = 1) : d34354 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d829, d277740, d34354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d829, d277740, d34354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d537 q = 1) (hb : d277739 q = 1) : d277854 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69651 q ha hb
    | true =>
      simp only [d537, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d538 q = 1) (hb : d277740 q = 1) : d277855 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d538, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h12 (q : Pattern) (ha : d830 q = 1) (hb : d277740 q = 1) : d278031 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d830, d278031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d830, d278031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d1091 q = 1) (hb : d277740 q = 1) : d278484 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1091, d278484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1091, d278484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d1092 q = 1) (hb : d277740 q = 1) : d278485 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1092, d278485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1092, d278485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1093 q = 1) (hb : d277739 q = 1) : d1093 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d1094 q = 1) (hb : d277739 q = 1) : d278486 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d278486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69612 q ha hb
    | true =>
      simp only [d1094, d278486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1095 q = 1) (hb : d277740 q = 1) : d278487 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d277740, d278487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d1095, d277740, d278487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h19 (q : Pattern) (ha : d1096 q = 1) (hb : d277740 q = 1) : d278488 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1096, d278488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1096, d278488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d133 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69592 q ha hb
    | true =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d134 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h22 (q : Pattern) (ha : d539 q = 1) (hb : d277740 q = 1) : d277856 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d539, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d1097 q = 1) (hb : d277740 q = 1) : d278489 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1097, d278489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d1097, d278489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d1098 q = 1) (hb : d277740 q = 1) : d278490 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1098, d278490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d1098, d278490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h25 (q : Pattern) (ha : d1099 q = 1) (hb : d277740 q = 1) : d278491 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1099, d278491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d1099, d278491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro69740 (p : Pattern) (ha : d9777 p = 1) (hb : d277740 p = 1) : d278510 p = 1 := by
  have h0 (q : Pattern) (ha : d1087 q = 1) (hb : d277739 q = 1) : d1087 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1088 q = 1) (hb : d277739 q = 1) : d278481 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d278481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69650 q ha hb
    | true =>
      simp only [d1088, d278481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1089 q = 1) (hb : d277740 q = 1) : d278482 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d277740, d278482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1089, d277740, d278482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9581 q = 1) (hb : d277739 q = 1) : d10057 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9581, d10057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69707 q ha hb
    | true =>
      simp only [d9581, d10057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9582 q = 1) (hb : d277740 q = 1) : d10058 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9582, d277740, d10058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9582, d277740, d10058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d9768 q = 1) (hb : d277740 q = 1) : d278507 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9768, d278507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9768, d278507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d9769 q = 1) (hb : d277740 q = 1) : d278508 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9769, d278508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9769, d278508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9770 q = 1) (hb : d277740 q = 1) : d278509 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9770, d278509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9770, d278509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h11 (q : Pattern) (ha : d9771 q = 1) (hb : d277739 q = 1) : d9771 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d9772 q = 1) (hb : d277739 q = 1) : d278496 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9772, d278496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69707 q ha hb
    | true =>
      simp only [d9772, d278496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9773 q = 1) (hb : d277740 q = 1) : d278497 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9773, d277740, d278497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9773, d277740, d278497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h14 (q : Pattern) (ha : d9452 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69653 q ha hb
    | true =>
      simp only [d9452, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d9453 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9453, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h16 (q : Pattern) (ha : d9774 q = 1) (hb : d277740 q = 1) : d278498 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9774, d278498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9774, d278498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9775 q = 1) (hb : d277740 q = 1) : d278499 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9775, d278499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9775, d278499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h18 (q : Pattern) (ha : d9776 q = 1) (hb : d277740 q = 1) : d278500 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9776, d278500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d9776, d278500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h19 (q : Pattern) (ha : d9777 q = 1) (hb : d277740 q = 1) : d278510 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9777, d278510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9777, d278510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro69741 (p : Pattern) (ha : d9788 p = 1) (hb : d277740 p = 1) : d278501 p = 1 := by
  have h0 (q : Pattern) (ha : d1087 q = 1) (hb : d277739 q = 1) : d1087 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1088 q = 1) (hb : d277739 q = 1) : d278481 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d278481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69650 q ha hb
    | true =>
      simp only [d1088, d278481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1089 q = 1) (hb : d277740 q = 1) : d278482 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d277740, d278482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1089, d277740, d278482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1093 q = 1) (hb : d277739 q = 1) : d1093 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1094 q = 1) (hb : d277739 q = 1) : d278486 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d278486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69612 q ha hb
    | true =>
      simp only [d1094, d278486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1095 q = 1) (hb : d277740 q = 1) : d278487 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d277740, d278487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1095, d277740, d278487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d1096 q = 1) (hb : d277740 q = 1) : d278488 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1096, d278488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1096, d278488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d537 q = 1) (hb : d277739 q = 1) : d277854 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69651 q ha hb
    | true =>
      simp only [d537, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d538 q = 1) (hb : d277740 q = 1) : d277855 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d538, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d133 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69592 q ha hb
    | true =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h12 (q : Pattern) (ha : d134 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d539 q = 1) (hb : d277740 q = 1) : d277856 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d539, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1097 q = 1) (hb : d277740 q = 1) : d278489 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1097, d278489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1097, d278489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d1098 q = 1) (hb : d277740 q = 1) : d278490 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1098, d278490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1098, d278490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d9771 q = 1) (hb : d277739 q = 1) : d9771 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d9772 q = 1) (hb : d277739 q = 1) : d278496 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9772, d278496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69707 q ha hb
    | true =>
      simp only [d9772, d278496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d9773 q = 1) (hb : d277740 q = 1) : d278497 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9773, d277740, d278497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d9773, d277740, d278497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h20 (q : Pattern) (ha : d9452 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69653 q ha hb
    | true =>
      simp only [d9452, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h21 (q : Pattern) (ha : d9453 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d9453, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h22 (q : Pattern) (ha : d9774 q = 1) (hb : d277740 q = 1) : d278498 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9774, d278498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d9774, d278498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d9775 q = 1) (hb : d277740 q = 1) : d278499 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9775, d278499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d9775, d278499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h24 (q : Pattern) (ha : d9776 q = 1) (hb : d277740 q = 1) : d278500 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9776, d278500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d9776, d278500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h25 (q : Pattern) (ha : d9788 q = 1) (hb : d277740 q = 1) : d278501 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9788, d278501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d9788, d278501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro69742 (p : Pattern) (ha : d9799 p = 1) (hb : d277740 p = 1) : d278519 p = 1 := by
  have h0 (q : Pattern) (ha : d1093 q = 1) (hb : d277739 q = 1) : d1093 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1094 q = 1) (hb : d277739 q = 1) : d278486 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d278486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69612 q ha hb
    | true =>
      simp only [d1094, d278486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1095 q = 1) (hb : d277740 q = 1) : d278487 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d277740, d278487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1095, d277740, d278487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9452 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9452, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69653 q ha hb
    | true =>
      simp only [d9452, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d9453 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9453, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9453, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d9795 q = 1) (hb : d277740 q = 1) : d278515 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9795, d278515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9795, d278515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d133 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69592 q ha hb
    | true =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d134 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d9796 q = 1) (hb : d277740 q = 1) : d278516 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9796, d278516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9796, d278516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9797 q = 1) (hb : d277740 q = 1) : d278517 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9797, d278517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d9797, d278517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d9798 q = 1) (hb : d277740 q = 1) : d278518 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9798, d278518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d9798, d278518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h14 (q : Pattern) (ha : d1119 q = 1) (hb : d277740 q = 1) : d1119 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d9799 q = 1) (hb : d277740 q = 1) : d278519 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9799, d278519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d9799, d278519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro69743 (p : Pattern) (ha : d16442 p = 1) (hb : d277740 p = 1) : d278525 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1100 q = 1) (hb : d277740 q = 1) : d278492 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1100, d278492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69739 q ha hb
    | true =>
      simp only [d1100, d278492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1101 q = 1) (hb : d277740 q = 1) : d278493 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1101, d278493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1101, d278493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1102 q = 1) (hb : d277740 q = 1) : d278494 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1102, d278494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1102, d278494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1103 q = 1) (hb : d277740 q = 1) : d278495 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1103, d278495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1103, d278495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9789 q = 1) (hb : d277740 q = 1) : d278502 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9789, d278502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69741 q ha hb
    | true =>
      simp only [d9789, d278502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9791 q = 1) (hb : d277740 q = 1) : d278503 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9791, d278503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d9791, d278503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16438 q = 1) (hb : d277740 q = 1) : d278504 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16438, d278504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16438, d278504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16439 q = 1) (hb : d277740 q = 1) : d278505 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16439, d278505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16439, d278505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16440 q = 1) (hb : d277740 q = 1) : d278506 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16440, d278506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16440, d278506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9778 q = 1) (hb : d277740 q = 1) : d278511 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9778, d278511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69740 q ha hb
    | true =>
      simp only [d9778, d278511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9780 q = 1) (hb : d277740 q = 1) : d278512 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9780, d278512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9780, d278512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14758 q = 1) (hb : d277740 q = 1) : d278513 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14758, d278513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14758, d278513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14759 q = 1) (hb : d277740 q = 1) : d278514 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14759, d278514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14759, d278514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d9800 q = 1) (hb : d277740 q = 1) : d278520 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d278520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69742 q ha hb
    | true =>
      simp only [d9800, d278520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d9802 q = 1) (hb : d277740 q = 1) : d278521 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d278521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d9802, d278521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d14763 q = 1) (hb : d277740 q = 1) : d278522 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d278522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14763, d278522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d14764 q = 1) (hb : d277740 q = 1) : d278523 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d278523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d14764, d278523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d16441 q = 1) (hb : d277740 q = 1) : d278524 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d16441, d278524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d16441, d278524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d16442 q = 1) (hb : d277740 q = 1) : d278525 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16442, d278525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16442, d278525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro69744 (p : Pattern) (ha : d1109 p = 1) (hb : d277740 p = 1) : d278531 p = 1 := by
  have h0 (q : Pattern) (ha : d1087 q = 1) (hb : d277739 q = 1) : d1087 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1088 q = 1) (hb : d277739 q = 1) : d278481 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1088, d278481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69650 q ha hb
    | true =>
      simp only [d1088, d278481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1089 q = 1) (hb : d277740 q = 1) : d278482 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1089, d277740, d278482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1089, d277740, d278482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1093 q = 1) (hb : d277739 q = 1) : d1093 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d1094 q = 1) (hb : d277739 q = 1) : d278486 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1094, d278486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69612 q ha hb
    | true =>
      simp only [d1094, d278486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1095 q = 1) (hb : d277740 q = 1) : d278487 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1095, d277740, d278487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1095, d277740, d278487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h7 (q : Pattern) (ha : d1096 q = 1) (hb : d277740 q = 1) : d278488 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1096, d278488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1096, d278488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d277739 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d537 q = 1) (hb : d277739 q = 1) : d277854 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d537, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69651 q ha hb
    | true =>
      simp only [d537, d277854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d538 q = 1) (hb : d277740 q = 1) : d277855 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d538, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d538, d277740, d277855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h11 (q : Pattern) (ha : d133 q = 1) (hb : d277739 q = 1) : d277742 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69592 q ha hb
    | true =>
      simp only [d133, d277742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h12 (q : Pattern) (ha : d134 q = 1) (hb : d277740 q = 1) : d277743 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d134, d277740, d277743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d539 q = 1) (hb : d277740 q = 1) : d277856 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d539, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d539, d277856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1097 q = 1) (hb : d277740 q = 1) : d278489 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1097, d278489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1097, d278489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d1098 q = 1) (hb : d277740 q = 1) : d278490 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1098, d278490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d1098, d278490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d18 q = 1) (hb : d277739 q = 1) : d18 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d1104 q = 1) (hb : d277739 q = 1) : d278526 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1104, d278526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69592 q ha hb
    | true =>
      simp only [d1104, d278526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1105 q = 1) (hb : d277740 q = 1) : d278527 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1105, d277740, d278527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d1105, d277740, d278527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h20 (q : Pattern) (ha : d1106 q = 1) (hb : d277740 q = 1) : d278528 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1106, d278528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1106, d278528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d20 q = 1) (hb : d277740 q = 1) : d20 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d135 q = 1) (hb : d277740 q = 1) : d277744 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d135, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d135, d277744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d1107 q = 1) (hb : d277740 q = 1) : d278529 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1107, d278529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d1107, d278529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d1108 q = 1) (hb : d277740 q = 1) : d278530 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1108, d278530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d1108, d278530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h25 (q : Pattern) (ha : d1109 q = 1) (hb : d277740 q = 1) : d278531 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d1109, d278531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1109, d278531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro69745 (p : Pattern) (ha : d16443 p = 1) (hb : d277740 p = 1) : d278543 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1110 q = 1) (hb : d277740 q = 1) : d278532 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1110, d278532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69744 q ha hb
    | true =>
      simp only [d1110, d278532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1111 q = 1) (hb : d277740 q = 1) : d278533 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1111, d278533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1111, d278533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1112 q = 1) (hb : d277740 q = 1) : d278534 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1112, d278534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1112, d278534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d1113 q = 1) (hb : d277740 q = 1) : d278535 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1113, d278535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1113, d278535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1121 q = 1) (hb : d277740 q = 1) : d278537 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1121, d278537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69737 q ha hb
    | true =>
      simp only [d1121, d278537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1122 q = 1) (hb : d277740 q = 1) : d278538 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1122, d278538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1122, d278538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1123 q = 1) (hb : d277740 q = 1) : d278539 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1123, d278539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1123, d278539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1124 q = 1) (hb : d277740 q = 1) : d278540 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1124, d278540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1124, d278540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1125 q = 1) (hb : d277740 q = 1) : d278541 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1125, d278541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1125, d278541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d9800 q = 1) (hb : d277740 q = 1) : d278520 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9800, d278520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69742 q ha hb
    | true =>
      simp only [d9800, d278520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d9802 q = 1) (hb : d277740 q = 1) : d278521 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9802, d278521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d9802, d278521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d14763 q = 1) (hb : d277740 q = 1) : d278522 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14763, d278522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14763, d278522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d14764 q = 1) (hb : d277740 q = 1) : d278523 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14764, d278523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d14764, d278523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d14765 q = 1) (hb : d277740 q = 1) : d278542 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14765, d278542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d14765, d278542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d16443 q = 1) (hb : d277740 q = 1) : d278543 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d16443, d278543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d16443, d278543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro69746 (p : Pattern) (ha : d16456 p = 1) (hb : d277740 p = 1) : d278555 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d277740 q = 1) : d278544 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d278544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69743 q ha hb
    | true =>
      simp only [d16444, d278544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69745 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d277740 q = 1) : d278545 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d278545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d278545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d277740 q = 1) : d278546 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d278546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d278546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d277740 q = 1) : d278549 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d278549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69745 q ha hb
    | true =>
      simp only [d16447, d278549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69736 q ha hb
  have h5 (q : Pattern) (ha : d16448 q = 1) (hb : d277740 q = 1) : d278550 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d278550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d278550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16449 q = 1) (hb : d277740 q = 1) : d278551 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d278551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d278551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16450 q = 1) (hb : d277740 q = 1) : d278552 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d278552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d278552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16451 q = 1) (hb : d277740 q = 1) : d278549 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d278549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69745 q ha hb
    | true =>
      simp only [d16451, d278549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69738 q ha hb
  have h9 (q : Pattern) (ha : d16452 q = 1) (hb : d277740 q = 1) : d278550 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16452, d278550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16452, d278550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16453 q = 1) (hb : d277740 q = 1) : d278551 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16453, d278551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16453, d278551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16454 q = 1) (hb : d277740 q = 1) : d278553 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16454, d278553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16454, d278553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16455 q = 1) (hb : d277740 q = 1) : d278554 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16455, d278554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16455, d278554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16456 q = 1) (hb : d277740 q = 1) : d278555 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16456, d278555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d16456, d278555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro69747 (p : Pattern) (ha : d16460 p = 1) (hb : d277740 p = 1) : d278559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16451 q = 1) (hb : d277740 q = 1) : d278549 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d278549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69745 q ha hb
    | true =>
      simp only [d16451, d278549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69738 q ha hb
  have h2 (q : Pattern) (ha : d16452 q = 1) (hb : d277740 q = 1) : d278550 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16452, d278550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16452, d278550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16453 q = 1) (hb : d277740 q = 1) : d278551 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16453, d278551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16453, d278551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16454 q = 1) (hb : d277740 q = 1) : d278553 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16454, d278553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16454, d278553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16459 q = 1) (hb : d277740 q = 1) : d278558 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16459, d278558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16459, d278558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16460 q = 1) (hb : d277740 q = 1) : d278559 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d16460, d278559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16460, d278559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro69748 (p : Pattern) (ha : d16466 p = 1) (hb : d277740 p = 1) : d278565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16457 q = 1) (hb : d277740 q = 1) : d278556 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16457, d278556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69746 q ha hb
    | true =>
      simp only [d16457, d278556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16458 q = 1) (hb : d277740 q = 1) : d278557 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16458, d278557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16458, d278557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16461 q = 1) (hb : d277740 q = 1) : d278560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d278560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69747 q ha hb
    | true =>
      simp only [d16461, d278560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16462 q = 1) (hb : d277740 q = 1) : d278561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d278561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d278561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d16463 q = 1) (hb : d277740 q = 1) : d278562 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16463, d278562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16463, d278562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16464 q = 1) (hb : d277740 q = 1) : d278563 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16464, d278563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d16464, d278563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d16465 q = 1) (hb : d277740 q = 1) : d278564 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16465, d278564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16465, d278564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d16466 q = 1) (hb : d277740 q = 1) : d278565 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16466, d278565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16466, d278565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro69749 (p : Pattern) (ha : d16470 p = 1) (hb : d277740 p = 1) : d278569 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d277740 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16461 q = 1) (hb : d277740 q = 1) : d278560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d16461, d278560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro69747 q ha hb
    | true =>
      simp only [d16461, d278560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d16462 q = 1) (hb : d277740 q = 1) : d278561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d16462, d278561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16462, d278561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16467 q = 1) (hb : d277740 q = 1) : d278566 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d16467, d278566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d16467, d278566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d16468 q = 1) (hb : d277740 q = 1) : d278567 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d16468, d278567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16468, d278567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16469 q = 1) (hb : d277740 q = 1) : d278568 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d16469, d278568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16469, d278568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d16470 q = 1) (hb : d277740 q = 1) : d278569 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d16470, d278569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16470, d278569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
