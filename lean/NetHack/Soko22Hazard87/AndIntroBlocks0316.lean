import NetHack.Soko22Hazard87.AndIntroBlocks0315
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro79000 (p : Pattern) (ha : d238968 p = 1) (hb : d282151 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29321 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d281159 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238957 q = 1) (hb : d281160 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238957, d281160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238957, d281160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d29328 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238958 q = 1) (hb : d281161 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238958, d281161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238958, d281161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d238966 q = 1) (hb : d281162 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238966, d281162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238966, d281162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238967 q = 1) (hb : d281163 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238967, d281163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238967, d281163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238968 q = 1) (hb : d282151 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238968, d282151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238968, d282151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79001 (p : Pattern) (ha : d238978 p = 1) (hb : d282162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29426 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282157 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238974 q = 1) (hb : d282158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238974, d282158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238974, d282158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d29496 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238975 q = 1) (hb : d282159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238975, d282159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238975, d282159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d238976 q = 1) (hb : d282160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238976, d282160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238976, d282160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238977 q = 1) (hb : d282161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238977, d282161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238977, d282161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238978 q = 1) (hb : d282162 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238978, d282162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238978, d282162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79002 (p : Pattern) (ha : d238984 p = 1) (hb : d282168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d29160 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238962 q = 1) (hb : d281165 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238962, d281165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78998 q ha hb
    | true =>
      simp only [d238962, d281165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78999 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29346 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238963 q = 1) (hb : d281166 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238963, d281166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238963, d281166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238964 q = 1) (hb : d282149 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238964, d282149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238964, d282149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238965 q = 1) (hb : d282150 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238965, d282150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238965, d282150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d238969 q = 1) (hb : d282152 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238969, d282152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238969, d282152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79000 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d29355 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d238970 q = 1) (hb : d282153 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238970, d282153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d238970, d282153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d238971 q = 1) (hb : d282154 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238971, d282154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d238971, d282154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d238972 q = 1) (hb : d282155 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238972, d282155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d238972, d282155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d238973 q = 1) (hb : d282156 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238973, d282156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d238973, d282156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d238979 q = 1) (hb : d282163 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d238979, d282163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238979, d282163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79001 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d29512 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d238980 q = 1) (hb : d282164 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d238980, d282164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d238980, d282164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d238981 q = 1) (hb : d282165 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d238981, d282165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d238981, d282165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d238982 q = 1) (hb : d282166 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d238982, d282166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d238982, d282166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d238983 q = 1) (hb : d282167 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d238983, d282167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d238983, d282167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d238984 q = 1) (hb : d282168 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d238984, d282168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d238984, d282168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro79003 (p : Pattern) (ha : d238990 p = 1) (hb : d282174 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d238985 q = 1) (hb : d282169 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d238985, d282169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238985, d282169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79002 q ha hb
  have h2 (q : Pattern) (ha : d238986 q = 1) (hb : d282170 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d238986, d282170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238986, d282170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d238987 q = 1) (hb : d282171 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d238987, d282171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238987, d282171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d238988 q = 1) (hb : d282172 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d238988, d282172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238988, d282172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d238989 q = 1) (hb : d282173 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d238989, d282173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238989, d282173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238990 q = 1) (hb : d282174 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d238990, d282174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238990, d282174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79004 (p : Pattern) (ha : d238998 p = 1) (hb : d281448 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29649 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29658 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d29688 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d281443 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d238994 q = 1) (hb : d281444 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238994, d281444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d238994, d281444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d29816 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d238995 q = 1) (hb : d281445 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238995, d281445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d238995, d281445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d238996 q = 1) (hb : d281446 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238996, d281446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d238996, d281446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d238997 q = 1) (hb : d281447 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238997, d281447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238997, d281447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d238998 q = 1) (hb : d281448 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d238998, d281448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238998, d281448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro79005 (p : Pattern) (ha : d239003 p = 1) (hb : d281458 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d29649 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29658 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29688 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d281443 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d238994 q = 1) (hb : d281444 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238994, d281444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d238994, d281444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d29816 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d238995 q = 1) (hb : d281445 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d238995, d281445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d238995, d281445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d238996 q = 1) (hb : d281446 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d238996, d281446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238996, d281446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d238997 q = 1) (hb : d281447 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d238997, d281447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d238997, d281447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d29826 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d29831 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d29833 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d281453 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d238999 q = 1) (hb : d281454 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238999, d281454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d238999, d281454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d29840 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d239000 q = 1) (hb : d281455 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d239000, d281455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d239000, d281455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d239001 q = 1) (hb : d281456 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d239001, d281456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d239001, d281456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d239002 q = 1) (hb : d281457 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d239002, d281457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d239002, d281457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d239003 q = 1) (hb : d281458 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d239003, d281458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d239003, d281458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro79006 (p : Pattern) (ha : d239010 p = 1) (hb : d282180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29833 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d281453 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d238999 q = 1) (hb : d281454 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d238999, d281454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d238999, d281454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d29840 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d239000 q = 1) (hb : d281455 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d239000, d281455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239000, d281455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d239008 q = 1) (hb : d281456 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d239008, d281456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239008, d281456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d239009 q = 1) (hb : d281457 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d239009, d281457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239009, d281457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d239010 q = 1) (hb : d282180 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d239010, d282180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239010, d282180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79007 (p : Pattern) (ha : d239020 p = 1) (hb : d282191 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d29956 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282186 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d239016 q = 1) (hb : d282187 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d239016, d282187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d239016, d282187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d30045 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d239017 q = 1) (hb : d282188 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d239017, d282188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239017, d282188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d239018 q = 1) (hb : d282189 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d239018, d282189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239018, d282189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d239019 q = 1) (hb : d282190 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d239019, d282190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239019, d282190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d239020 q = 1) (hb : d282191 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d239020, d282191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239020, d282191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79008 (p : Pattern) (ha : d239026 p = 1) (hb : d282197 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d29641 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239004 q = 1) (hb : d281459 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d239004, d281459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79004 q ha hb
    | true =>
      simp only [d239004, d281459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79005 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d29858 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d239005 q = 1) (hb : d281460 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d239005, d281460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239005, d281460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d239006 q = 1) (hb : d282178 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d239006, d282178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239006, d282178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239007 q = 1) (hb : d282179 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d239007, d282179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d239007, d282179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d239011 q = 1) (hb : d282181 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d239011, d282181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239011, d282181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79006 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d29867 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d239012 q = 1) (hb : d282182 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d239012, d282182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d239012, d282182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d239013 q = 1) (hb : d282183 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d239013, d282183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d239013, d282183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d239014 q = 1) (hb : d282184 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d239014, d282184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d239014, d282184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d239015 q = 1) (hb : d282185 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d239015, d282185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d239015, d282185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d239021 q = 1) (hb : d282192 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d239021, d282192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239021, d282192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79007 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d30061 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d239022 q = 1) (hb : d282193 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d239022, d282193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d239022, d282193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d239023 q = 1) (hb : d282194 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d239023, d282194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d239023, d282194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d239024 q = 1) (hb : d282195 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d239024, d282195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d239024, d282195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d239025 q = 1) (hb : d282196 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d239025, d282196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d239025, d282196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d239026 q = 1) (hb : d282197 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d239026, d282197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d239026, d282197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro79009 (p : Pattern) (ha : d239032 p = 1) (hb : d282203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239027 q = 1) (hb : d282198 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d239027, d282198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239027, d282198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79008 q ha hb
  have h2 (q : Pattern) (ha : d239028 q = 1) (hb : d282199 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d239028, d282199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239028, d282199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d239029 q = 1) (hb : d282200 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d239029, d282200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239029, d282200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d239030 q = 1) (hb : d282201 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d239030, d282201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239030, d282201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d239031 q = 1) (hb : d282202 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d239031, d282202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239031, d282202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239032 q = 1) (hb : d282203 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d239032, d282203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239032, d282203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79010 (p : Pattern) (ha : d239041 p = 1) (hb : d281770 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30188 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30197 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d30221 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d281765 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d239037 q = 1) (hb : d281766 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d239037, d281766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d239037, d281766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d30343 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d239038 q = 1) (hb : d281767 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d239038, d281767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239038, d281767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d239039 q = 1) (hb : d281768 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d239039, d281768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d239039, d281768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d239040 q = 1) (hb : d281769 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d239040, d281769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d239040, d281769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d239041 q = 1) (hb : d281770 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d239041, d281770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239041, d281770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro79011 (p : Pattern) (ha : d239046 p = 1) (hb : d281780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30188 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30197 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30221 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d281765 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d239037 q = 1) (hb : d281766 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d239037, d281766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d239037, d281766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d30343 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d239038 q = 1) (hb : d281767 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d239038, d281767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239038, d281767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d239039 q = 1) (hb : d281768 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d239039, d281768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d239039, d281768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d239040 q = 1) (hb : d281769 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d239040, d281769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d239040, d281769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d30353 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d30358 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d30360 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d281775 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d239042 q = 1) (hb : d281776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d239042, d281776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d239042, d281776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d30367 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d239043 q = 1) (hb : d281777 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d239043, d281777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d239043, d281777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d239044 q = 1) (hb : d281778 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d239044, d281778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d239044, d281778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d239045 q = 1) (hb : d281779 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d239045, d281779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d239045, d281779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d239046 q = 1) (hb : d281780 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d239046, d281780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d239046, d281780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro79012 (p : Pattern) (ha : d239053 p = 1) (hb : d282210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30360 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d281775 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d239042 q = 1) (hb : d281776 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d239042, d281776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d239042, d281776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d30367 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d239043 q = 1) (hb : d281777 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d239043, d281777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239043, d281777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d239051 q = 1) (hb : d281778 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d239051, d281778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239051, d281778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d239052 q = 1) (hb : d281779 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d239052, d281779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239052, d281779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d239053 q = 1) (hb : d282210 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d239053, d282210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239053, d282210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79013 (p : Pattern) (ha : d239063 p = 1) (hb : d282221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30474 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d282216 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d239059 q = 1) (hb : d282217 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d239059, d282217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d239059, d282217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d30559 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d239060 q = 1) (hb : d282218 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d239060, d282218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239060, d282218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d239061 q = 1) (hb : d282219 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d239061, d282219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239061, d282219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d239062 q = 1) (hb : d282220 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d239062, d282220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239062, d282220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d239063 q = 1) (hb : d282221 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d239063, d282221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239063, d282221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79014 (p : Pattern) (ha : d239069 p = 1) (hb : d282227 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d30180 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239047 q = 1) (hb : d281781 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d239047, d281781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79010 q ha hb
    | true =>
      simp only [d239047, d281781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79011 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d30385 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d239048 q = 1) (hb : d281782 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d239048, d281782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239048, d281782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d239049 q = 1) (hb : d282208 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d239049, d282208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239049, d282208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239050 q = 1) (hb : d282209 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d239050, d282209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d239050, d282209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d239054 q = 1) (hb : d282211 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d239054, d282211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239054, d282211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79012 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d30394 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d239055 q = 1) (hb : d282212 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d239055, d282212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d239055, d282212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d239056 q = 1) (hb : d282213 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d239056, d282213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d239056, d282213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d239057 q = 1) (hb : d282214 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d239057, d282214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d239057, d282214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d239058 q = 1) (hb : d282215 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d239058, d282215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d239058, d282215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d239064 q = 1) (hb : d282222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d239064, d282222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239064, d282222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79013 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d30575 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d239065 q = 1) (hb : d282223 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d239065, d282223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d239065, d282223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d239066 q = 1) (hb : d282224 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d239066, d282224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d239066, d282224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d239067 q = 1) (hb : d282225 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d239067, d282225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d239067, d282225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d239068 q = 1) (hb : d282226 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d239068, d282226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d239068, d282226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d239069 q = 1) (hb : d282227 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d239069, d282227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d239069, d282227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro79015 (p : Pattern) (ha : d239075 p = 1) (hb : d282233 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239070 q = 1) (hb : d282228 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d239070, d282228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239070, d282228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79014 q ha hb
  have h2 (q : Pattern) (ha : d239071 q = 1) (hb : d282229 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d239071, d282229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239071, d282229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d239072 q = 1) (hb : d282230 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d239072, d282230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239072, d282230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d239073 q = 1) (hb : d282231 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d239073, d282231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239073, d282231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d239074 q = 1) (hb : d282232 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d239074, d282232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239074, d282232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d239075 q = 1) (hb : d282233 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d239075, d282233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d239075, d282233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79016 (p : Pattern) (ha : d239081 p = 1) (hb : d282239 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d238910 q = 1) (hb : d282120 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d238910, d282120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78985 q ha hb
    | true =>
      simp only [d238910, d282120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78991 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d238950 q = 1) (hb : d282147 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d238950, d282147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238950, d282147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro78997 q ha hb
  have h3 (q : Pattern) (ha : d238951 q = 1) (hb : d282148 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d238951, d282148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d238951, d282148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d238991 q = 1) (hb : d282175 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d238991, d282175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238991, d282175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79003 q ha hb
  have h5 (q : Pattern) (ha : d238992 q = 1) (hb : d282176 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d238992, d282176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d238992, d282176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d238993 q = 1) (hb : d282177 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d238993, d282177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d238993, d282177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d239033 q = 1) (hb : d282204 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d239033, d282204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239033, d282204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79009 q ha hb
  have h8 (q : Pattern) (ha : d239034 q = 1) (hb : d282205 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d239034, d282205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239034, d282205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d239035 q = 1) (hb : d282206 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d239035, d282206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239035, d282206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d239036 q = 1) (hb : d282207 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d239036, d282207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d239036, d282207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d239076 q = 1) (hb : d282234 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d239076, d282234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239076, d282234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79015 q ha hb
  have h12 (q : Pattern) (ha : d239077 q = 1) (hb : d282235 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d239077, d282235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239077, d282235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d239078 q = 1) (hb : d282236 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d239078, d282236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239078, d282236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d239079 q = 1) (hb : d282237 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d239079, d282237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239079, d282237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d239080 q = 1) (hb : d282238 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d239080, d282238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d239080, d282238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d239081 q = 1) (hb : d282239 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d239081, d282239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d239081, d282239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro79017 (p : Pattern) (ha : d239087 p = 1) (hb : d282245 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239082 q = 1) (hb : d282240 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d239082, d282240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79016 q ha hb
    | true =>
      simp only [d239082, d282240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239083 q = 1) (hb : d282241 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d239083, d282241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239083, d282241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d239084 q = 1) (hb : d282242 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d239084, d282242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d239084, d282242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239085 q = 1) (hb : d282243 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d239085, d282243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239085, d282243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d239086 q = 1) (hb : d282244 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d239086, d282244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239086, d282244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d239087 q = 1) (hb : d282245 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d239087, d282245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239087, d282245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79018 (p : Pattern) (ha : d239093 p = 1) (hb : d282251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239088 q = 1) (hb : d282246 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d239088, d282246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79017 q ha hb
    | true =>
      simp only [d239088, d282246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239089 q = 1) (hb : d282247 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d239089, d282247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239089, d282247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d239090 q = 1) (hb : d282248 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d239090, d282248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d239090, d282248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239091 q = 1) (hb : d282249 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d239091, d282249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239091, d282249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d239092 q = 1) (hb : d282250 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d239092, d282250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239092, d282250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d239093 q = 1) (hb : d282251 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d239093, d282251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239093, d282251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79019 (p : Pattern) (ha : d239099 p = 1) (hb : d282257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239094 q = 1) (hb : d282252 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d239094, d282252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79018 q ha hb
    | true =>
      simp only [d239094, d282252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239095 q = 1) (hb : d282253 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d239095, d282253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239095, d282253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d239096 q = 1) (hb : d282254 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d239096, d282254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d239096, d282254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239097 q = 1) (hb : d282255 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d239097, d282255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239097, d282255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d239098 q = 1) (hb : d282256 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d239098, d282256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239098, d282256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d239099 q = 1) (hb : d282257 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d239099, d282257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239099, d282257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79020 (p : Pattern) (ha : d239105 p = 1) (hb : d282263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239100 q = 1) (hb : d282258 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d239100, d282258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79019 q ha hb
    | true =>
      simp only [d239100, d282258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239101 q = 1) (hb : d282259 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d239101, d282259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239101, d282259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d239102 q = 1) (hb : d282260 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d239102, d282260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d239102, d282260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239103 q = 1) (hb : d282261 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d239103, d282261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239103, d282261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d239104 q = 1) (hb : d282262 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d239104, d282262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239104, d282262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d239105 q = 1) (hb : d282263 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d239105, d282263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239105, d282263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79021 (p : Pattern) (ha : d239111 p = 1) (hb : d282269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239106 q = 1) (hb : d282264 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d239106, d282264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79020 q ha hb
    | true =>
      simp only [d239106, d282264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239107 q = 1) (hb : d282265 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d239107, d282265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239107, d282265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d239108 q = 1) (hb : d282266 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d239108, d282266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d239108, d282266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239109 q = 1) (hb : d282267 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d239109, d282267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239109, d282267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d239110 q = 1) (hb : d282268 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d239110, d282268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239110, d282268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d239111 q = 1) (hb : d282269 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d239111, d282269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239111, d282269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79022 (p : Pattern) (ha : d239117 p = 1) (hb : d282275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239112 q = 1) (hb : d282270 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d239112, d282270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79021 q ha hb
    | true =>
      simp only [d239112, d282270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239113 q = 1) (hb : d282271 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d239113, d282271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239113, d282271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d239114 q = 1) (hb : d282272 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d239114, d282272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d239114, d282272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239115 q = 1) (hb : d282273 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d239115, d282273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239115, d282273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d239116 q = 1) (hb : d282274 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d239116, d282274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239116, d282274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d239117 q = 1) (hb : d282275 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d239117, d282275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239117, d282275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79023 (p : Pattern) (ha : d239123 p = 1) (hb : d282281 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d239118 q = 1) (hb : d282276 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d239118, d282276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79022 q ha hb
    | true =>
      simp only [d239118, d282276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d239119 q = 1) (hb : d282277 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d239119, d282277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d239119, d282277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d239120 q = 1) (hb : d282278 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d239120, d282278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d239120, d282278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d239121 q = 1) (hb : d282279 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d239121, d282279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d239121, d282279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d239122 q = 1) (hb : d282280 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d239122, d282280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d239122, d282280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d239123 q = 1) (hb : d282281 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d239123, d282281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d239123, d282281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79024 (p : Pattern) (ha : d30638 p = 1) (hb : d241832 p = 1) : d30758 p = 1 := by
  have h0 (q : Pattern) (ha : d30635 q = 1) (hb : d241831 q = 1) : d30635 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30636 q = 1) (hb : d241832 q = 1) : d30756 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30636, d241832, d30756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30636, d241832, d30756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30637 q = 1) (hb : d241832 q = 1) : d30757 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30637, d30757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30637, d30757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d23 q = 1) (hb : d241832 q = 1) : d23 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30638 q = 1) (hb : d241832 q = 1) : d30758 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30638, d30758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30638, d30758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79025 (p : Pattern) (ha : d30644 p = 1) (hb : d241832 p = 1) : d30999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30639 q = 1) (hb : d241832 q = 1) : d30759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30639, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79024 q ha hb
    | true =>
      simp only [d30639, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30640 q = 1) (hb : d241832 q = 1) : d30760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30640, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30640, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30641 q = 1) (hb : d241832 q = 1) : d30761 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30641, d30761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30641, d30761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30642 q = 1) (hb : d241832 q = 1) : d30762 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30642, d30762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30642, d30762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d28 q = 1) (hb : d241832 q = 1) : d28 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30643 q = 1) (hb : d241832 q = 1) : d30763 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30643, d30763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30643, d30763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d29 q = 1) (hb : d241832 q = 1) : d29 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30644 q = 1) (hb : d241832 q = 1) : d30999 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30644, d30999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30644, d30999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79026 (p : Pattern) (ha : d30650 p = 1) (hb : d241832 p = 1) : d243740 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d241832 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30645 q = 1) (hb : d241832 q = 1) : d243735 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30645, d243735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79025 q ha hb
    | true =>
      simp only [d30645, d243735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30646 q = 1) (hb : d241832 q = 1) : d243736 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30646, d243736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30646, d243736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30647 q = 1) (hb : d241832 q = 1) : d243737 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30647, d243737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30647, d243737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d33 q = 1) (hb : d241832 q = 1) : d33 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30648 q = 1) (hb : d241832 q = 1) : d243738 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30648, d243738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30648, d243738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d34 q = 1) (hb : d241832 q = 1) : d34 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30649 q = 1) (hb : d241832 q = 1) : d243739 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d30649, d243739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30649, d243739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30650 q = 1) (hb : d241832 q = 1) : d243740 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d30650, d243740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30650, d243740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro79027 (p : Pattern) (ha : d30656 p = 1) (hb : d241832 p = 1) : d243746 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d241832 q = 1) : d243741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79026 q ha hb
    | true =>
      simp only [d30651, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d241832 q = 1) : d243742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d241832 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30653 q = 1) (hb : d241832 q = 1) : d243743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30653, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30653, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30654 q = 1) (hb : d241832 q = 1) : d243744 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30654, d243744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30654, d243744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30655 q = 1) (hb : d241832 q = 1) : d243745 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30655, d243745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30655, d243745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30656 q = 1) (hb : d241832 q = 1) : d243746 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30656, d243746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30656, d243746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro79028 (p : Pattern) (ha : d241832 p = 1) (hb : d245354 p = 1) : d243752 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d241832 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d241832 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d241832 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30657 q = 1) (hb : d241832 q = 1) : d243747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30657, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79027 q ha hb
    | true =>
      simp only [d30657, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d245350 q = 1) : d243748 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245350, d243748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d245350, d243748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d241832 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d245351 q = 1) : d243749 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245351, d243749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245351, d243749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d245352 q = 1) : d243750 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245352, d243750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245352, d243750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d245353 q = 1) : d243751 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245353, d243751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245353, d243751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d241832 q = 1) (hb : d245354 q = 1) : d243752 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245354, d243752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245354, d243752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro79029 (p : Pattern) (ha : d30663 p = 1) (hb : d241832 p = 1) : d243753 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d241832 q = 1) : d243741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79026 q ha hb
    | true =>
      simp only [d30651, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d241832 q = 1) : d243742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d241832 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30653 q = 1) (hb : d241832 q = 1) : d243743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30653, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30653, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30654 q = 1) (hb : d241832 q = 1) : d243744 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30654, d243744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30654, d243744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30655 q = 1) (hb : d241832 q = 1) : d243745 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30655, d243745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30655, d243745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30663 q = 1) (hb : d241832 q = 1) : d243753 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30663, d243753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30663, d243753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro79030 (p : Pattern) (ha : d241832 p = 1) (hb : d245359 p = 1) : d243759 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d241832 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d241832 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d241832 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d30657 q = 1) (hb : d241832 q = 1) : d243747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30657, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79027 q ha hb
    | true =>
      simp only [d30657, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d245350 q = 1) : d243748 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245350, d243748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d245350, d243748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d241832 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d245351 q = 1) : d243749 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245351, d243749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d245351, d243749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d245352 q = 1) : d243750 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245352, d243750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245352, d243750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d245353 q = 1) : d243751 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245353, d243751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245353, d243751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d241832 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d241832 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d241832 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d30664 q = 1) (hb : d241832 q = 1) : d243754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30664, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79029 q ha hb
    | true =>
      simp only [d30664, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d245355 q = 1) : d243755 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245355, d243755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d245355, d243755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d241832 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d241832 q = 1) (hb : d245356 q = 1) : d243756 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245356, d243756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245356, d243756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d241832 q = 1) (hb : d245357 q = 1) : d243757 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245357, d243757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d245357, d243757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d241832 q = 1) (hb : d245358 q = 1) : d243758 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245358, d243758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245358, d243758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d241832 q = 1) (hb : d245359 q = 1) : d243759 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245359, d243759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245359, d243759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro79031 (p : Pattern) (ha : d241832 p = 1) (hb : d245366 p = 1) : d243766 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d241832 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30664 q = 1) (hb : d241832 q = 1) : d243754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30664, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79029 q ha hb
    | true =>
      simp only [d30664, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d245355 q = 1) : d243755 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245355, d243755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245355, d243755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d241832 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d245356 q = 1) : d243756 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245356, d243756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245356, d243756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d245364 q = 1) : d243764 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245364, d243764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245364, d243764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d245365 q = 1) : d243765 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245365, d243765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245365, d243765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d245366 q = 1) : d243766 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245366, d243766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245366, d243766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79032 (p : Pattern) (ha : d30687 p = 1) (hb : d241832 p = 1) : d31136 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30682 q = 1) (hb : d241832 q = 1) : d30852 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30682, d30852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30682, d30852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79024 q ha hb
  have h2 (q : Pattern) (ha : d30639 q = 1) (hb : d241832 q = 1) : d30759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30639, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79024 q ha hb
    | true =>
      simp only [d30639, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30683 q = 1) (hb : d241832 q = 1) : d30853 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30683, d30853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30683, d30853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30640 q = 1) (hb : d241832 q = 1) : d30760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30640, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30640, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30684 q = 1) (hb : d241832 q = 1) : d30854 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30684, d30854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30684, d30854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30685 q = 1) (hb : d241832 q = 1) : d30855 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30685, d30855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30685, d30855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d69 q = 1) (hb : d241832 q = 1) : d69 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30686 q = 1) (hb : d241832 q = 1) : d30856 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30686, d30856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30686, d30856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70 q = 1) (hb : d241832 q = 1) : d70 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d30687 q = 1) (hb : d241832 q = 1) : d31136 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30687, d31136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30687, d31136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro79033 (p : Pattern) (ha : d30693 p = 1) (hb : d241832 p = 1) : d243777 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d241832 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30688 q = 1) (hb : d241832 q = 1) : d243772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30688, d243772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79032 q ha hb
    | true =>
      simp only [d30688, d243772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30689 q = 1) (hb : d241832 q = 1) : d243773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30689, d243773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30689, d243773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30690 q = 1) (hb : d241832 q = 1) : d243774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30690, d243774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30690, d243774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74 q = 1) (hb : d241832 q = 1) : d74 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30691 q = 1) (hb : d241832 q = 1) : d243775 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30691, d243775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30691, d243775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d75 q = 1) (hb : d241832 q = 1) : d75 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30692 q = 1) (hb : d241832 q = 1) : d243776 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d30692, d243776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30692, d243776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30693 q = 1) (hb : d241832 q = 1) : d243777 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d30693, d243777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30693, d243777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h9 p ha hb
theorem andIntro79034 (p : Pattern) (ha : d30699 p = 1) (hb : d241832 p = 1) : d243783 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30694 q = 1) (hb : d241832 q = 1) : d243778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30694, d243778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79033 q ha hb
    | true =>
      simp only [d30694, d243778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30695 q = 1) (hb : d241832 q = 1) : d243779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30695, d243779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30695, d243779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d241832 q = 1) : d79 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30696 q = 1) (hb : d241832 q = 1) : d243780 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30696, d243780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30696, d243780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30697 q = 1) (hb : d241832 q = 1) : d243781 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30697, d243781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30697, d243781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30698 q = 1) (hb : d241832 q = 1) : d243782 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30698, d243782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30698, d243782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30699 q = 1) (hb : d241832 q = 1) : d243783 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30699, d243783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30699, d243783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro79035 (p : Pattern) (ha : d241832 p = 1) (hb : d245376 p = 1) : d243789 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d241832 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30700 q = 1) (hb : d241832 q = 1) : d243784 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30700, d243784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79034 q ha hb
    | true =>
      simp only [d30700, d243784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d245372 q = 1) : d243785 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245372, d243785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d245372, d243785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d241832 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d245373 q = 1) : d243786 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245373, d243786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245373, d243786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d245374 q = 1) : d243787 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245374, d243787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245374, d243787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d245375 q = 1) : d243788 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245375, d243788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245375, d243788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d245376 q = 1) : d243789 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245376, d243789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245376, d243789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79036 (p : Pattern) (ha : d241832 p = 1) (hb : d245382 p = 1) : d243795 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d241832 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d245360 q = 1) : d243760 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245360, d243760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79028 q ha hb
    | true =>
      simp only [d245360, d243760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79030 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d241832 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d245361 q = 1) : d243761 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245361, d243761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d245361, d243761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d245362 q = 1) : d243762 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245362, d243762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d245362, d243762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d245363 q = 1) : d243763 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245363, d243763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245363, d243763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d245367 q = 1) : d243767 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245367, d243767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d245367, d243767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79031 q ha hb
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d245368 q = 1) : d243768 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245368, d243768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d245368, d243768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d245369 q = 1) : d243769 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245369, d243769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245369, d243769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d241832 q = 1) (hb : d245370 q = 1) : d243770 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245370, d243770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245370, d243770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d241832 q = 1) (hb : d245371 q = 1) : d243771 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245371, d243771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245371, d243771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d241832 q = 1) (hb : d245377 q = 1) : d243790 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245377, d243790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d245377, d243790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79035 q ha hb
  have h13 (q : Pattern) (ha : d241832 q = 1) (hb : d245378 q = 1) : d243791 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245378, d243791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245378, d243791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d245379 q = 1) : d243792 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245379, d243792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245379, d243792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d241832 q = 1) (hb : d245380 q = 1) : d243793 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245380, d243793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245380, d243793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d241832 q = 1) (hb : d245381 q = 1) : d243794 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245381, d243794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245381, d243794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d241832 q = 1) (hb : d245382 q = 1) : d243795 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245382, d243795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245382, d243795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro79037 (p : Pattern) (ha : d30721 p = 1) (hb : d241832 p = 1) : d243805 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d241832 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30657 q = 1) (hb : d241832 q = 1) : d243747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30657, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79027 q ha hb
    | true =>
      simp only [d30657, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30717 q = 1) (hb : d241832 q = 1) : d243801 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30717, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30717, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30718 q = 1) (hb : d241832 q = 1) : d243802 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30718, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30718, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30719 q = 1) (hb : d241832 q = 1) : d243803 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30719, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30719, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30720 q = 1) (hb : d241832 q = 1) : d243804 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30720, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30720, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30721 q = 1) (hb : d241832 q = 1) : d243805 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d30721, d243805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30721, d243805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro79038 (p : Pattern) (ha : d30728 p = 1) (hb : d241832 p = 1) : d243812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d241832 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30657 q = 1) (hb : d241832 q = 1) : d243747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30657, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79027 q ha hb
    | true =>
      simp only [d30657, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30717 q = 1) (hb : d241832 q = 1) : d243801 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30717, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30717, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30718 q = 1) (hb : d241832 q = 1) : d243802 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30718, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30718, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30719 q = 1) (hb : d241832 q = 1) : d243803 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30719, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30719, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30720 q = 1) (hb : d241832 q = 1) : d243804 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30720, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30720, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d241832 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30664 q = 1) (hb : d241832 q = 1) : d243754 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30664, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79029 q ha hb
    | true =>
      simp only [d30664, d243754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30724 q = 1) (hb : d241832 q = 1) : d243808 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30724, d243808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30724, d243808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30725 q = 1) (hb : d241832 q = 1) : d243809 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30725, d243809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30725, d243809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30726 q = 1) (hb : d241832 q = 1) : d243810 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30726, d243810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30726, d243810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30727 q = 1) (hb : d241832 q = 1) : d243811 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30727, d243811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30727, d243811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d30728 q = 1) (hb : d241832 q = 1) : d243812 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d30728, d243812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30728, d243812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro79039 (p : Pattern) (ha : d30834 p = 1) (hb : d241832 p = 1) : d243873 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d241832 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30657 q = 1) (hb : d241832 q = 1) : d243747 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30657, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79027 q ha hb
    | true =>
      simp only [d30657, d243747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30717 q = 1) (hb : d241832 q = 1) : d243801 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30717, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30717, d243801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30718 q = 1) (hb : d241832 q = 1) : d243802 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30718, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30718, d243802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30719 q = 1) (hb : d241832 q = 1) : d243803 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30719, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30719, d243803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30720 q = 1) (hb : d241832 q = 1) : d243804 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30720, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30720, d243804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d241832 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30834 q = 1) (hb : d241832 q = 1) : d243873 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d30834, d243873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30834, d243873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79040 (p : Pattern) (ha : d30733 p = 1) (hb : d241832 p = 1) : d243817 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d241832 q = 1) : d243741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79026 q ha hb
    | true =>
      simp only [d30651, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d241832 q = 1) : d243742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d241832 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30653 q = 1) (hb : d241832 q = 1) : d243743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30653, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30653, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30654 q = 1) (hb : d241832 q = 1) : d243744 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30654, d243744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30654, d243744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30732 q = 1) (hb : d241832 q = 1) : d243816 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30732, d243816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30732, d243816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30733 q = 1) (hb : d241832 q = 1) : d243817 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30733, d243817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30733, d243817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro79041 (p : Pattern) (ha : d30740 p = 1) (hb : d241832 p = 1) : d243824 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d241832 q = 1) : d243741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79026 q ha hb
    | true =>
      simp only [d30651, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d241832 q = 1) : d243742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d241832 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30653 q = 1) (hb : d241832 q = 1) : d243743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30653, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30653, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30738 q = 1) (hb : d241832 q = 1) : d243822 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30738, d243822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30738, d243822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30739 q = 1) (hb : d241832 q = 1) : d243823 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30739, d243823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30739, d243823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30740 q = 1) (hb : d241832 q = 1) : d243824 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30740, d243824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30740, d243824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro79042 (p : Pattern) (ha : d30750 p = 1) (hb : d241832 p = 1) : d30989 p = 1 := by
  have h0 (q : Pattern) (ha : d30747 q = 1) (hb : d241831 q = 1) : d30747 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30635 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30748 q = 1) (hb : d241832 q = 1) : d30987 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30748, d241832, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30748, d241832, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30749 q = 1) (hb : d241832 q = 1) : d30988 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30749, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30749, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30635 q = 1) (hb : d241831 q = 1) : d30635 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d30636 q = 1) (hb : d241832 q = 1) : d30756 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30636, d241832, d30756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30636, d241832, d30756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d30637 q = 1) (hb : d241832 q = 1) : d30757 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30637, d30757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30637, d30757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d30750 q = 1) (hb : d241832 q = 1) : d30989 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30750, d30989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30750, d30989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro79043 (p : Pattern) (ha : d30764 p = 1) (hb : d241832 p = 1) : d243828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30751 q = 1) (hb : d241832 q = 1) : d30990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30751, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79042 q ha hb
    | true =>
      simp only [d30751, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30752 q = 1) (hb : d241832 q = 1) : d30991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30752, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30752, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30753 q = 1) (hb : d241832 q = 1) : d30992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30753, d30992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30753, d30992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30754 q = 1) (hb : d241832 q = 1) : d30993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30754, d30993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30754, d30993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30639 q = 1) (hb : d241832 q = 1) : d30759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30639, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79024 q ha hb
    | true =>
      simp only [d30639, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30640 q = 1) (hb : d241832 q = 1) : d30760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30640, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30640, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30641 q = 1) (hb : d241832 q = 1) : d30761 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30641, d30761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30641, d30761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30642 q = 1) (hb : d241832 q = 1) : d30762 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30642, d30762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30642, d30762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30755 q = 1) (hb : d241832 q = 1) : d30994 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30755, d30994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30755, d30994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30763 q = 1) (hb : d241832 q = 1) : d30763 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d30764 q = 1) (hb : d241832 q = 1) : d243828 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30764, d243828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30764, d243828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79044 (p : Pattern) (ha : d30770 p = 1) (hb : d241832 p = 1) : d243834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30765 q = 1) (hb : d241832 q = 1) : d243829 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30765, d243829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79043 q ha hb
    | true =>
      simp only [d30765, d243829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79025 q ha hb
  have h2 (q : Pattern) (ha : d30766 q = 1) (hb : d241832 q = 1) : d243830 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30766, d243830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30766, d243830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30767 q = 1) (hb : d241832 q = 1) : d243831 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30767, d243831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30767, d243831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d241832 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d30645 q = 1) (hb : d241832 q = 1) : d243735 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30645, d243735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79025 q ha hb
    | true =>
      simp only [d30645, d243735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30646 q = 1) (hb : d241832 q = 1) : d243736 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30646, d243736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30646, d243736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30647 q = 1) (hb : d241832 q = 1) : d243737 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30647, d243737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30647, d243737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30768 q = 1) (hb : d241832 q = 1) : d243832 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30768, d243832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30768, d243832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d33 q = 1) (hb : d241832 q = 1) : d33 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d30648 q = 1) (hb : d241832 q = 1) : d243738 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30648, d243738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30648, d243738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30769 q = 1) (hb : d241832 q = 1) : d243833 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d30769, d243833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30769, d243833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30770 q = 1) (hb : d241832 q = 1) : d243834 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d30770, d243834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30770, d243834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro79045 (p : Pattern) (ha : d30776 p = 1) (hb : d241832 p = 1) : d243840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30771 q = 1) (hb : d241832 q = 1) : d243835 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30771, d243835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79044 q ha hb
    | true =>
      simp only [d30771, d243835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30772 q = 1) (hb : d241832 q = 1) : d243836 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30772, d243836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30772, d243836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30651 q = 1) (hb : d241832 q = 1) : d243741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79026 q ha hb
    | true =>
      simp only [d30651, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30652 q = 1) (hb : d241832 q = 1) : d243742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30773 q = 1) (hb : d241832 q = 1) : d243837 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30773, d243837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30773, d243837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30774 q = 1) (hb : d241832 q = 1) : d243838 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30774, d243838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30774, d243838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30775 q = 1) (hb : d241832 q = 1) : d243839 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30775, d243839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30775, d243839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30776 q = 1) (hb : d241832 q = 1) : d243840 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30776, d243840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30776, d243840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79046 (p : Pattern) (ha : d30805 p = 1) (hb : d241832 p = 1) : d243846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d241832 q = 1) : d243741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79026 q ha hb
    | true =>
      simp only [d30651, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d241832 q = 1) : d243742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30802 q = 1) (hb : d241832 q = 1) : d243843 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30802, d243843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30802, d243843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30803 q = 1) (hb : d241832 q = 1) : d243844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30803, d243844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30803, d243844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30804 q = 1) (hb : d241832 q = 1) : d243845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30804, d243845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30804, d243845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30805 q = 1) (hb : d241832 q = 1) : d243846 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30805, d243846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30805, d243846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79047 (p : Pattern) (ha : d241832 p = 1) (hb : d245392 p = 1) : d243852 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d241832 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30734 q = 1) (hb : d241832 q = 1) : d243818 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30734, d243818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79040 q ha hb
    | true =>
      simp only [d30734, d243818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30735 q = 1) (hb : d241832 q = 1) : d243819 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30735, d243819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30735, d243819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30736 q = 1) (hb : d241832 q = 1) : d243820 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30736, d243820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30736, d243820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30737 q = 1) (hb : d241832 q = 1) : d243821 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30737, d243821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30737, d243821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d241832 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d30741 q = 1) (hb : d241832 q = 1) : d243825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30741, d243825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79041 q ha hb
    | true =>
      simp only [d30741, d243825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30742 q = 1) (hb : d241832 q = 1) : d243826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30742, d243826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30742, d243826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30743 q = 1) (hb : d241832 q = 1) : d243827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30743, d243827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30743, d243827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30777 q = 1) (hb : d241832 q = 1) : d243841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30777, d243841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79045 q ha hb
    | true =>
      simp only [d30777, d243841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79027 q ha hb
  have h11 (q : Pattern) (ha : d241832 q = 1) (hb : d245388 q = 1) : d243842 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245388, d243842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245388, d243842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d30806 q = 1) (hb : d241832 q = 1) : d243847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30806, d243847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79046 q ha hb
    | true =>
      simp only [d30806, d243847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30807 q = 1) (hb : d241832 q = 1) : d243848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30807, d243848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30807, d243848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d245389 q = 1) : d243849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245389, d243849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245389, d243849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d241832 q = 1) (hb : d245390 q = 1) : d243850 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245390, d243850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245390, d243850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d241832 q = 1) (hb : d245391 q = 1) : d243851 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245391, d243851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d245391, d243851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d241832 q = 1) (hb : d245392 q = 1) : d243852 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245392, d243852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245392, d243852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro79048 (p : Pattern) (ha : d30812 p = 1) (hb : d241832 p = 1) : d243853 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d241832 q = 1) : d243741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79026 q ha hb
    | true =>
      simp only [d30651, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d241832 q = 1) : d243742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d241832 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30653 q = 1) (hb : d241832 q = 1) : d243743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30653, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30653, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30654 q = 1) (hb : d241832 q = 1) : d243744 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30654, d243744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30654, d243744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30732 q = 1) (hb : d241832 q = 1) : d243816 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30732, d243816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30732, d243816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30812 q = 1) (hb : d241832 q = 1) : d243853 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30812, d243853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30812, d243853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro79049 (p : Pattern) (ha : d30817 p = 1) (hb : d241832 p = 1) : d243858 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d241832 q = 1) : d243741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79026 q ha hb
    | true =>
      simp only [d30651, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d241832 q = 1) : d243742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d241832 q = 1) : d38 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30653 q = 1) (hb : d241832 q = 1) : d243743 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30653, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30653, d243743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30738 q = 1) (hb : d241832 q = 1) : d243822 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30738, d243822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30738, d243822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30739 q = 1) (hb : d241832 q = 1) : d243823 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30739, d243823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30739, d243823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30817 q = 1) (hb : d241832 q = 1) : d243858 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30817, d243858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30817, d243858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro79050 (p : Pattern) (ha : d30821 p = 1) (hb : d241832 p = 1) : d243862 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30771 q = 1) (hb : d241832 q = 1) : d243835 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30771, d243835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79044 q ha hb
    | true =>
      simp only [d30771, d243835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30772 q = 1) (hb : d241832 q = 1) : d243836 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30772, d243836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30772, d243836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30651 q = 1) (hb : d241832 q = 1) : d243741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79026 q ha hb
    | true =>
      simp only [d30651, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30652 q = 1) (hb : d241832 q = 1) : d243742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30773 q = 1) (hb : d241832 q = 1) : d243837 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30773, d243837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30773, d243837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30774 q = 1) (hb : d241832 q = 1) : d243838 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30774, d243838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30774, d243838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30775 q = 1) (hb : d241832 q = 1) : d243839 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30775, d243839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30775, d243839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30821 q = 1) (hb : d241832 q = 1) : d243862 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30821, d243862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30821, d243862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79051 (p : Pattern) (ha : d30826 p = 1) (hb : d241832 p = 1) : d243865 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30651 q = 1) (hb : d241832 q = 1) : d243741 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30651, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79026 q ha hb
    | true =>
      simp only [d30651, d243741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30652 q = 1) (hb : d241832 q = 1) : d243742 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30652, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30652, d243742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30802 q = 1) (hb : d241832 q = 1) : d243843 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30802, d243843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30802, d243843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30803 q = 1) (hb : d241832 q = 1) : d243844 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30803, d243844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30803, d243844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30804 q = 1) (hb : d241832 q = 1) : d243845 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30804, d243845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30804, d243845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30826 q = 1) (hb : d241832 q = 1) : d243865 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30826, d243865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30826, d243865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79052 (p : Pattern) (ha : d241832 p = 1) (hb : d245397 p = 1) : d243871 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d241832 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30734 q = 1) (hb : d241832 q = 1) : d243818 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30734, d243818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79040 q ha hb
    | true =>
      simp only [d30734, d243818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30735 q = 1) (hb : d241832 q = 1) : d243819 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30735, d243819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30735, d243819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30736 q = 1) (hb : d241832 q = 1) : d243820 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30736, d243820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30736, d243820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30737 q = 1) (hb : d241832 q = 1) : d243821 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30737, d243821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30737, d243821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d241832 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d30741 q = 1) (hb : d241832 q = 1) : d243825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30741, d243825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79041 q ha hb
    | true =>
      simp only [d30741, d243825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30742 q = 1) (hb : d241832 q = 1) : d243826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30742, d243826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30742, d243826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30743 q = 1) (hb : d241832 q = 1) : d243827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30743, d243827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30743, d243827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30777 q = 1) (hb : d241832 q = 1) : d243841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30777, d243841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79045 q ha hb
    | true =>
      simp only [d30777, d243841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79027 q ha hb
  have h11 (q : Pattern) (ha : d241832 q = 1) (hb : d245388 q = 1) : d243842 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245388, d243842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d245388, d243842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d30806 q = 1) (hb : d241832 q = 1) : d243847 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30806, d243847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79046 q ha hb
    | true =>
      simp only [d30806, d243847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30807 q = 1) (hb : d241832 q = 1) : d243848 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30807, d243848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d30807, d243848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d245389 q = 1) : d243849 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245389, d243849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245389, d243849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d241832 q = 1) (hb : d245390 q = 1) : d243850 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245390, d243850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d245390, d243850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d241832 q = 1) (hb : d245391 q = 1) : d243851 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245391, d243851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d245391, d243851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d194 q = 1) (hb : d241832 q = 1) : d194 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d30813 q = 1) (hb : d241832 q = 1) : d243854 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30813, d243854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79048 q ha hb
    | true =>
      simp only [d30813, d243854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d30814 q = 1) (hb : d241832 q = 1) : d243855 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30814, d243855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30814, d243855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d30815 q = 1) (hb : d241832 q = 1) : d243856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30815, d243856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d30815, d243856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d30816 q = 1) (hb : d241832 q = 1) : d243857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30816, d243857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30816, d243857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d199 q = 1) (hb : d241832 q = 1) : d199 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d30818 q = 1) (hb : d241832 q = 1) : d243859 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30818, d243859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79049 q ha hb
    | true =>
      simp only [d30818, d243859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d30819 q = 1) (hb : d241832 q = 1) : d243860 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30819, d243860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30819, d243860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d30820 q = 1) (hb : d241832 q = 1) : d243861 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30820, d243861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d30820, d243861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d30822 q = 1) (hb : d241832 q = 1) : d243863 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30822, d243863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79050 q ha hb
    | true =>
      simp only [d30822, d243863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79029 q ha hb
  have h27 (q : Pattern) (ha : d241832 q = 1) (hb : d245393 q = 1) : d243864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245393, d243864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
    | true =>
      simp only [d245393, d243864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d30827 q = 1) (hb : d241832 q = 1) : d243866 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30827, d243866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79051 q ha hb
    | true =>
      simp only [d30827, d243866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d30828 q = 1) (hb : d241832 q = 1) : d243867 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30828, d243867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
    | true =>
      simp only [d30828, d243867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h30 (q : Pattern) (ha : d241832 q = 1) (hb : d245394 q = 1) : d243868 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245394, d243868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d245394, d243868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
  have h31 (q : Pattern) (ha : d241832 q = 1) (hb : d245395 q = 1) : d243869 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245395, d243869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d245395, d243869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d241832 q = 1) (hb : d245396 q = 1) : d243870 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245396, d243870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d245396, d243870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d241832 q = 1) (hb : d245397 q = 1) : d243871 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245397, d243871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245397, d243871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro79053 (p : Pattern) (ha : d241832 p = 1) (hb : d245404 p = 1) : d243880 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30822 q = 1) (hb : d241832 q = 1) : d243863 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30822, d243863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79050 q ha hb
    | true =>
      simp only [d30822, d243863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79029 q ha hb
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d245393 q = 1) : d243864 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245393, d243864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245393, d243864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d30827 q = 1) (hb : d241832 q = 1) : d243866 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30827, d243866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79051 q ha hb
    | true =>
      simp only [d30827, d243866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30828 q = 1) (hb : d241832 q = 1) : d243867 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30828, d243867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30828, d243867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d245394 q = 1) : d243868 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245394, d243868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245394, d243868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d245402 q = 1) : d243878 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245402, d243878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245402, d243878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d245403 q = 1) : d243879 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245403, d243879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245403, d243879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d245404 q = 1) : d243880 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245404, d243880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245404, d243880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79054 (p : Pattern) (ha : d30857 p = 1) (hb : d241832 p = 1) : d243886 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30847 q = 1) (hb : d241832 q = 1) : d31127 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30847, d31127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30847, d31127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79042 q ha hb
  have h2 (q : Pattern) (ha : d30751 q = 1) (hb : d241832 q = 1) : d30990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30751, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79042 q ha hb
    | true =>
      simp only [d30751, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30848 q = 1) (hb : d241832 q = 1) : d31128 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30848, d31128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30848, d31128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30752 q = 1) (hb : d241832 q = 1) : d30991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30752, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30752, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30849 q = 1) (hb : d241832 q = 1) : d31129 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30849, d31129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30849, d31129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30850 q = 1) (hb : d241832 q = 1) : d31130 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30850, d31130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30850, d31130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30682 q = 1) (hb : d241832 q = 1) : d30852 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30682, d30852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30682, d30852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79024 q ha hb
  have h8 (q : Pattern) (ha : d30639 q = 1) (hb : d241832 q = 1) : d30759 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30639, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79024 q ha hb
    | true =>
      simp only [d30639, d30759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30683 q = 1) (hb : d241832 q = 1) : d30853 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30683, d30853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30683, d30853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30640 q = 1) (hb : d241832 q = 1) : d30760 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30640, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30640, d30760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d30684 q = 1) (hb : d241832 q = 1) : d30854 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30684, d30854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30684, d30854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30685 q = 1) (hb : d241832 q = 1) : d30855 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30685, d30855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30685, d30855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d30851 q = 1) (hb : d241832 q = 1) : d31131 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30851, d31131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30851, d31131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d30856 q = 1) (hb : d241832 q = 1) : d30856 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d30857 q = 1) (hb : d241832 q = 1) : d243886 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30857, d243886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d30857, d243886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79055 (p : Pattern) (ha : d30863 p = 1) (hb : d241832 p = 1) : d243892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30858 q = 1) (hb : d241832 q = 1) : d243887 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30858, d243887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79054 q ha hb
    | true =>
      simp only [d30858, d243887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79032 q ha hb
  have h2 (q : Pattern) (ha : d30859 q = 1) (hb : d241832 q = 1) : d243888 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30859, d243888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30859, d243888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30860 q = 1) (hb : d241832 q = 1) : d243889 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30860, d243889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30860, d243889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d241832 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d30688 q = 1) (hb : d241832 q = 1) : d243772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30688, d243772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79032 q ha hb
    | true =>
      simp only [d30688, d243772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30689 q = 1) (hb : d241832 q = 1) : d243773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30689, d243773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30689, d243773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30690 q = 1) (hb : d241832 q = 1) : d243774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30690, d243774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30690, d243774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30861 q = 1) (hb : d241832 q = 1) : d243890 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30861, d243890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30861, d243890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74 q = 1) (hb : d241832 q = 1) : d74 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d30691 q = 1) (hb : d241832 q = 1) : d243775 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30691, d243775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30691, d243775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30862 q = 1) (hb : d241832 q = 1) : d243891 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d30862, d243891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30862, d243891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30863 q = 1) (hb : d241832 q = 1) : d243892 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d30863, d243892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30863, d243892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h12 p ha hb
theorem andIntro79056 (p : Pattern) (ha : d30869 p = 1) (hb : d241832 p = 1) : d243898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30864 q = 1) (hb : d241832 q = 1) : d243893 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30864, d243893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79055 q ha hb
    | true =>
      simp only [d30864, d243893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30865 q = 1) (hb : d241832 q = 1) : d243894 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30865, d243894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30865, d243894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30694 q = 1) (hb : d241832 q = 1) : d243778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30694, d243778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79033 q ha hb
    | true =>
      simp only [d30694, d243778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30695 q = 1) (hb : d241832 q = 1) : d243779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30695, d243779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30695, d243779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30866 q = 1) (hb : d241832 q = 1) : d243895 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30866, d243895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30866, d243895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30867 q = 1) (hb : d241832 q = 1) : d243896 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30867, d243896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30867, d243896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30868 q = 1) (hb : d241832 q = 1) : d243897 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30868, d243897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30868, d243897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30869 q = 1) (hb : d241832 q = 1) : d243898 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30869, d243898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30869, d243898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79057 (p : Pattern) (ha : d30894 p = 1) (hb : d241832 p = 1) : d243904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30694 q = 1) (hb : d241832 q = 1) : d243778 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30694, d243778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79033 q ha hb
    | true =>
      simp only [d30694, d243778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30695 q = 1) (hb : d241832 q = 1) : d243779 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30695, d243779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30695, d243779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30891 q = 1) (hb : d241832 q = 1) : d243901 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30891, d243901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30891, d243901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30892 q = 1) (hb : d241832 q = 1) : d243902 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30892, d243902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30892, d243902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30893 q = 1) (hb : d241832 q = 1) : d243903 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30893, d243903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30893, d243903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30894 q = 1) (hb : d241832 q = 1) : d243904 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30894, d243904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30894, d243904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79058 (p : Pattern) (ha : d241832 p = 1) (hb : d245414 p = 1) : d243910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30870 q = 1) (hb : d241832 q = 1) : d243899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30870, d243899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79056 q ha hb
    | true =>
      simp only [d30870, d243899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79034 q ha hb
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d245410 q = 1) : d243900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245410, d243900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245410, d243900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d30895 q = 1) (hb : d241832 q = 1) : d243905 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30895, d243905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79057 q ha hb
    | true =>
      simp only [d30895, d243905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30896 q = 1) (hb : d241832 q = 1) : d243906 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30896, d243906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30896, d243906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d245411 q = 1) : d243907 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245411, d243907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245411, d243907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d245412 q = 1) : d243908 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245412, d243908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245412, d243908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d245413 q = 1) : d243909 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245413, d243909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245413, d243909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d245414 q = 1) : d243910 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245414, d243910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245414, d243910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79059 (p : Pattern) (ha : d241832 p = 1) (hb : d245420 p = 1) : d243916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30722 q = 1) (hb : d241832 q = 1) : d243806 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30722, d243806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30722, d243806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79037 q ha hb
  have h2 (q : Pattern) (ha : d30723 q = 1) (hb : d241832 q = 1) : d243807 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30723, d243807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30723, d243807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30729 q = 1) (hb : d241832 q = 1) : d243813 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30729, d243813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79037 q ha hb
    | true =>
      simp only [d30729, d243813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79038 q ha hb
  have h4 (q : Pattern) (ha : d30730 q = 1) (hb : d241832 q = 1) : d243814 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30730, d243814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30730, d243814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30731 q = 1) (hb : d241832 q = 1) : d243815 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d30731, d243815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30731, d243815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d245398 q = 1) : d243872 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245398, d243872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79047 q ha hb
    | true =>
      simp only [d245398, d243872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79052 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d241832 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d30835 q = 1) (hb : d241832 q = 1) : d243874 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30835, d243874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79039 q ha hb
    | true =>
      simp only [d30835, d243874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d245399 q = 1) : d243875 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245399, d243875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245399, d243875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d241832 q = 1) (hb : d245400 q = 1) : d243876 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245400, d243876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245400, d243876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d241832 q = 1) (hb : d245401 q = 1) : d243877 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245401, d243877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d245401, d243877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d241832 q = 1) (hb : d245405 q = 1) : d243881 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245405, d243881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245405, d243881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79053 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d241832 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d245406 q = 1) : d243882 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245406, d243882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d245406, d243882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d241832 q = 1) (hb : d245407 q = 1) : d243883 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245407, d243883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245407, d243883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d241832 q = 1) (hb : d245408 q = 1) : d243884 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245408, d243884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d245408, d243884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d241832 q = 1) (hb : d245409 q = 1) : d243885 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245409, d243885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245409, d243885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d241832 q = 1) (hb : d245415 q = 1) : d243911 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245415, d243911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245415, d243911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79058 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d241832 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d241832 q = 1) (hb : d245416 q = 1) : d243912 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245416, d243912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d245416, d243912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d241832 q = 1) (hb : d245417 q = 1) : d243913 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245417, d243913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d245417, d243913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d241832 q = 1) (hb : d245418 q = 1) : d243914 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245418, d243914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245418, d243914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d241832 q = 1) (hb : d245419 q = 1) : d243915 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245419, d243915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d245419, d243915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d241832 q = 1) (hb : d245420 q = 1) : d243916 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245420, d243916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245420, d243916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro79060 (p : Pattern) (ha : d241832 p = 1) (hb : d245426 p = 1) : d243922 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d241832 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d245383 q = 1) : d243796 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245383, d243796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245383, d243796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79036 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d245384 q = 1) : d243797 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245384, d243797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245384, d243797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d245385 q = 1) : d243798 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245385, d243798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245385, d243798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d245386 q = 1) : d243799 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245386, d243799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245386, d243799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d245387 q = 1) : d243800 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245387, d243800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245387, d243800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d245421 q = 1) : d243917 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245421, d243917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245421, d243917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79059 q ha hb
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d245422 q = 1) : d243918 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245422, d243918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245422, d243918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d245423 q = 1) : d243919 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245423, d243919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245423, d243919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d241832 q = 1) (hb : d245424 q = 1) : d243920 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245424, d243920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245424, d243920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d241832 q = 1) (hb : d245425 q = 1) : d243921 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245425, d243921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245425, d243921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d241832 q = 1) (hb : d245426 q = 1) : d243922 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245426, d243922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245426, d243922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro79061 (p : Pattern) (ha : d30915 p = 1) (hb : d241832 p = 1) : d243925 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30765 q = 1) (hb : d241832 q = 1) : d243829 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30765, d243829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79043 q ha hb
    | true =>
      simp only [d30765, d243829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79025 q ha hb
  have h2 (q : Pattern) (ha : d30766 q = 1) (hb : d241832 q = 1) : d243830 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30766, d243830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30766, d243830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30767 q = 1) (hb : d241832 q = 1) : d243831 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30767, d243831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30767, d243831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30 q = 1) (hb : d241832 q = 1) : d30 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d30645 q = 1) (hb : d241832 q = 1) : d243735 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30645, d243735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79025 q ha hb
    | true =>
      simp only [d30645, d243735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30646 q = 1) (hb : d241832 q = 1) : d243736 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30646, d243736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30646, d243736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30647 q = 1) (hb : d241832 q = 1) : d243737 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30647, d243737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30647, d243737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30768 q = 1) (hb : d241832 q = 1) : d243832 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30768, d243832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30768, d243832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30913 q = 1) (hb : d241832 q = 1) : d243923 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30913, d243923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30913, d243923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d30914 q = 1) (hb : d241832 q = 1) : d243924 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d30914, d243924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30914, d243924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30915 q = 1) (hb : d241832 q = 1) : d243925 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d30915, d243925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d30915, d243925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro79062 (p : Pattern) (ha : d30919 p = 1) (hb : d241832 p = 1) : d243929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30 q = 1) (hb : d241832 q = 1) : d30 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30645 q = 1) (hb : d241832 q = 1) : d243735 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30645, d243735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79025 q ha hb
    | true =>
      simp only [d30645, d243735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30646 q = 1) (hb : d241832 q = 1) : d243736 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30646, d243736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30646, d243736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30647 q = 1) (hb : d241832 q = 1) : d243737 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30647, d243737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30647, d243737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30913 q = 1) (hb : d241832 q = 1) : d243923 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30913, d243923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30913, d243923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30918 q = 1) (hb : d241832 q = 1) : d243928 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d30918, d243928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30918, d243928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30919 q = 1) (hb : d241832 q = 1) : d243929 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d30919, d243929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30919, d243929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro79063 (p : Pattern) (ha : d30925 p = 1) (hb : d241832 p = 1) : d243935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d241832 q = 1) : d243926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79061 q ha hb
    | true =>
      simp only [d30916, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d241832 q = 1) : d243927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30920 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79062 q ha hb
    | true =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30921 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30922 q = 1) (hb : d241832 q = 1) : d243932 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30922, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30922, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30923 q = 1) (hb : d241832 q = 1) : d243933 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30923, d243933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30923, d243933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30924 q = 1) (hb : d241832 q = 1) : d243934 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30924, d243934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30924, d243934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30925 q = 1) (hb : d241832 q = 1) : d243935 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30925, d243935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30925, d243935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79064 (p : Pattern) (ha : d30929 p = 1) (hb : d241832 p = 1) : d243939 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30920 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79062 q ha hb
    | true =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30921 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30926 q = 1) (hb : d241832 q = 1) : d243936 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30926, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30926, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30927 q = 1) (hb : d241832 q = 1) : d243937 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30927, d243937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30927, d243937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30928 q = 1) (hb : d241832 q = 1) : d243938 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30928, d243938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30928, d243938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30929 q = 1) (hb : d241832 q = 1) : d243939 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30929, d243939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30929, d243939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79065 (p : Pattern) (ha : d30935 p = 1) (hb : d241832 p = 1) : d243945 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30930 q = 1) (hb : d241832 q = 1) : d243940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30930, d243940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79063 q ha hb
    | true =>
      simp only [d30930, d243940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79064 q ha hb
  have h2 (q : Pattern) (ha : d30931 q = 1) (hb : d241832 q = 1) : d243941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30931, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30931, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30932 q = 1) (hb : d241832 q = 1) : d243942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30932, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30932, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30933 q = 1) (hb : d241832 q = 1) : d243943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30933, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30933, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30934 q = 1) (hb : d241832 q = 1) : d243944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30934, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30934, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30935 q = 1) (hb : d241832 q = 1) : d243945 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d30935, d243945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30935, d243945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79066 (p : Pattern) (ha : d30938 p = 1) (hb : d241832 p = 1) : d243948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d241832 q = 1) : d243926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79061 q ha hb
    | true =>
      simp only [d30916, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d241832 q = 1) : d243927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30920 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79062 q ha hb
    | true =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30921 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30922 q = 1) (hb : d241832 q = 1) : d243932 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30922, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30922, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30923 q = 1) (hb : d241832 q = 1) : d243933 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30923, d243933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30923, d243933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30924 q = 1) (hb : d241832 q = 1) : d243934 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30924, d243934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30924, d243934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30938 q = 1) (hb : d241832 q = 1) : d243948 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30938, d243948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30938, d243948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79067 (p : Pattern) (ha : d30939 p = 1) (hb : d241832 p = 1) : d243949 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30920 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79062 q ha hb
    | true =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30921 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30926 q = 1) (hb : d241832 q = 1) : d243936 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30926, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30926, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30927 q = 1) (hb : d241832 q = 1) : d243937 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30927, d243937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30927, d243937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30928 q = 1) (hb : d241832 q = 1) : d243938 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30928, d243938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30928, d243938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30939 q = 1) (hb : d241832 q = 1) : d243949 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30939, d243949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30939, d243949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79068 (p : Pattern) (ha : d30945 p = 1) (hb : d241832 p = 1) : d243955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30930 q = 1) (hb : d241832 q = 1) : d243940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30930, d243940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79063 q ha hb
    | true =>
      simp only [d30930, d243940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79064 q ha hb
  have h2 (q : Pattern) (ha : d30931 q = 1) (hb : d241832 q = 1) : d243941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30931, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30931, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30932 q = 1) (hb : d241832 q = 1) : d243942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30932, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30932, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30933 q = 1) (hb : d241832 q = 1) : d243943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30933, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30933, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30934 q = 1) (hb : d241832 q = 1) : d243944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30934, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30934, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30940 q = 1) (hb : d241832 q = 1) : d243950 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30940, d243950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79066 q ha hb
    | true =>
      simp only [d30940, d243950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79067 q ha hb
  have h7 (q : Pattern) (ha : d30941 q = 1) (hb : d241832 q = 1) : d243951 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30941, d243951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30941, d243951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30942 q = 1) (hb : d241832 q = 1) : d243952 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30942, d243952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30942, d243952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30943 q = 1) (hb : d241832 q = 1) : d243953 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30943, d243953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30943, d243953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30944 q = 1) (hb : d241832 q = 1) : d243954 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30944, d243954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30944, d243954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30945 q = 1) (hb : d241832 q = 1) : d243955 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d30945, d243955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30945, d243955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79069 (p : Pattern) (ha : d31097 p = 1) (hb : d241832 p = 1) : d244028 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30930 q = 1) (hb : d241832 q = 1) : d243940 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30930, d243940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79063 q ha hb
    | true =>
      simp only [d30930, d243940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79064 q ha hb
  have h2 (q : Pattern) (ha : d30931 q = 1) (hb : d241832 q = 1) : d243941 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30931, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30931, d243941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30932 q = 1) (hb : d241832 q = 1) : d243942 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30932, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30932, d243942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30933 q = 1) (hb : d241832 q = 1) : d243943 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30933, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30933, d243943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30934 q = 1) (hb : d241832 q = 1) : d243944 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d30934, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30934, d243944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31092 q = 1) (hb : d241832 q = 1) : d244023 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31092, d244023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79064 q ha hb
    | true =>
      simp only [d31092, d244023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31093 q = 1) (hb : d241832 q = 1) : d244024 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31093, d244024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31093, d244024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31094 q = 1) (hb : d241832 q = 1) : d244025 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31094, d244025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31094, d244025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31095 q = 1) (hb : d241832 q = 1) : d244026 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31095, d244026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31095, d244026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31096 q = 1) (hb : d241832 q = 1) : d244027 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31096, d244027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31096, d244027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31097 q = 1) (hb : d241832 q = 1) : d244028 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31097, d244028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31097, d244028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79070 (p : Pattern) (ha : d31103 p = 1) (hb : d241832 p = 1) : d244034 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31092 q = 1) (hb : d241832 q = 1) : d244023 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31092, d244023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79064 q ha hb
    | true =>
      simp only [d31092, d244023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31093 q = 1) (hb : d241832 q = 1) : d244024 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31093, d244024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31093, d244024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31094 q = 1) (hb : d241832 q = 1) : d244025 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31094, d244025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31094, d244025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31095 q = 1) (hb : d241832 q = 1) : d244026 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31095, d244026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31095, d244026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31096 q = 1) (hb : d241832 q = 1) : d244027 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31096, d244027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31096, d244027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31098 q = 1) (hb : d241832 q = 1) : d244029 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31098, d244029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79067 q ha hb
    | true =>
      simp only [d31098, d244029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31099 q = 1) (hb : d241832 q = 1) : d244030 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31099, d244030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31099, d244030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31100 q = 1) (hb : d241832 q = 1) : d244031 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31100, d244031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31100, d244031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31101 q = 1) (hb : d241832 q = 1) : d244032 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31101, d244032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31101, d244032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31102 q = 1) (hb : d241832 q = 1) : d244033 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31102, d244033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31102, d244033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31103 q = 1) (hb : d241832 q = 1) : d244034 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31103, d244034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31103, d244034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79071 (p : Pattern) (ha : d31112 p = 1) (hb : d241832 p = 1) : d244043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31098 q = 1) (hb : d241832 q = 1) : d244029 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31098, d244029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79067 q ha hb
    | true =>
      simp only [d31098, d244029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31099 q = 1) (hb : d241832 q = 1) : d244030 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31099, d244030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31099, d244030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31100 q = 1) (hb : d241832 q = 1) : d244031 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31100, d244031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31100, d244031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31101 q = 1) (hb : d241832 q = 1) : d244032 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31101, d244032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31101, d244032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31102 q = 1) (hb : d241832 q = 1) : d244033 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31102, d244033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31102, d244033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31112 q = 1) (hb : d241832 q = 1) : d244043 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31112, d244043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31112, d244043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79072 (p : Pattern) (ha : d31155 p = 1) (hb : d241832 p = 1) : d244068 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71 q = 1) (hb : d241832 q = 1) : d71 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30688 q = 1) (hb : d241832 q = 1) : d243772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30688, d243772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79032 q ha hb
    | true =>
      simp only [d30688, d243772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30689 q = 1) (hb : d241832 q = 1) : d243773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30689, d243773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30689, d243773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30690 q = 1) (hb : d241832 q = 1) : d243774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30690, d243774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30690, d243774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31145 q = 1) (hb : d241832 q = 1) : d244058 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31145, d244058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31145, d244058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31154 q = 1) (hb : d241832 q = 1) : d244067 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31154, d244067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31154, d244067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31155 q = 1) (hb : d241832 q = 1) : d244068 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31155, d244068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31155, d244068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h7 p ha hb
theorem andIntro79073 (p : Pattern) (ha : d31211 p = 1) (hb : d241832 p = 1) : d244091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31156 q = 1) (hb : d241832 q = 1) : d244069 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31156, d244069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79072 q ha hb
    | true =>
      simp only [d31156, d244069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31157 q = 1) (hb : d241832 q = 1) : d244070 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31157, d244070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31157, d244070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31208 q = 1) (hb : d241832 q = 1) : d244088 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31208, d244088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31208, d244088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31209 q = 1) (hb : d241832 q = 1) : d244089 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31209, d244089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31209, d244089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31210 q = 1) (hb : d241832 q = 1) : d244090 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31210, d244090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31210, d244090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31211 q = 1) (hb : d241832 q = 1) : d244091 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31211, d244091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31211, d244091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79074 (p : Pattern) (ha : d31217 p = 1) (hb : d241832 p = 1) : d244097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31212 q = 1) (hb : d241832 q = 1) : d244092 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31212, d244092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79073 q ha hb
    | true =>
      simp only [d31212, d244092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31213 q = 1) (hb : d241832 q = 1) : d244093 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31213, d244093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31213, d244093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31214 q = 1) (hb : d241832 q = 1) : d244094 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31214, d244094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31214, d244094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31215 q = 1) (hb : d241832 q = 1) : d244095 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31215, d244095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31215, d244095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31216 q = 1) (hb : d241832 q = 1) : d244096 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31216, d244096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31216, d244096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31217 q = 1) (hb : d241832 q = 1) : d244097 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31217, d244097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31217, d244097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79075 (p : Pattern) (ha : d30950 p = 1) (hb : d241832 p = 1) : d243960 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d241832 q = 1) : d243926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79061 q ha hb
    | true =>
      simp only [d30916, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d241832 q = 1) : d243927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30920 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79062 q ha hb
    | true =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30921 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30922 q = 1) (hb : d241832 q = 1) : d243932 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30922, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30922, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30923 q = 1) (hb : d241832 q = 1) : d243933 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30923, d243933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30923, d243933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30949 q = 1) (hb : d241832 q = 1) : d243959 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30949, d243959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30949, d243959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30950 q = 1) (hb : d241832 q = 1) : d243960 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30950, d243960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30950, d243960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79076 (p : Pattern) (ha : d30952 p = 1) (hb : d241832 p = 1) : d243962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30920 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79062 q ha hb
    | true =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30921 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30926 q = 1) (hb : d241832 q = 1) : d243936 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30926, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30926, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30927 q = 1) (hb : d241832 q = 1) : d243937 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30927, d243937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30927, d243937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30951 q = 1) (hb : d241832 q = 1) : d243961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30951, d243961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30951, d243961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30952 q = 1) (hb : d241832 q = 1) : d243962 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30952, d243962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30952, d243962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79077 (p : Pattern) (ha : d30959 p = 1) (hb : d241832 p = 1) : d243969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d241832 q = 1) : d243926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79061 q ha hb
    | true =>
      simp only [d30916, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d241832 q = 1) : d243927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30920 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79062 q ha hb
    | true =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30921 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30922 q = 1) (hb : d241832 q = 1) : d243932 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30922, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30922, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30957 q = 1) (hb : d241832 q = 1) : d243967 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30957, d243967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30957, d243967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30958 q = 1) (hb : d241832 q = 1) : d243968 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30958, d243968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30958, d243968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d30959 q = 1) (hb : d241832 q = 1) : d243969 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30959, d243969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30959, d243969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79078 (p : Pattern) (ha : d30962 p = 1) (hb : d241832 p = 1) : d243972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30920 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79062 q ha hb
    | true =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30921 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30926 q = 1) (hb : d241832 q = 1) : d243936 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30926, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30926, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30960 q = 1) (hb : d241832 q = 1) : d243970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30960, d243970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30960, d243970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30961 q = 1) (hb : d241832 q = 1) : d243971 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30961, d243971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30961, d243971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30962 q = 1) (hb : d241832 q = 1) : d243972 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d30962, d243972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30962, d243972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79079 (p : Pattern) (ha : d30976 p = 1) (hb : d241832 p = 1) : d31325 p = 1 := by
  have h0 (q : Pattern) (ha : d30969 q = 1) (hb : d241831 q = 1) : d30969 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30973 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30974 q = 1) (hb : d241832 q = 1) : d31323 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30974, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30974, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30975 q = 1) (hb : d241832 q = 1) : d31324 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30975, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30975, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30747 q = 1) (hb : d241831 q = 1) : d30747 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d30635 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d30748 q = 1) (hb : d241832 q = 1) : d30987 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30748, d241832, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30748, d241832, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d30749 q = 1) (hb : d241832 q = 1) : d30988 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30749, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30749, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d30976 q = 1) (hb : d241832 q = 1) : d31325 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30976, d31325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30976, d31325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro79080 (p : Pattern) (ha : d30981 p = 1) (hb : d241832 p = 1) : d30989 p = 1 := by
  have h0 (q : Pattern) (ha : d30747 q = 1) (hb : d241831 q = 1) : d30747 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30635 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30748 q = 1) (hb : d241832 q = 1) : d30987 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30748, d241832, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30748, d241832, d30987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30749 q = 1) (hb : d241832 q = 1) : d30988 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30749, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30749, d30988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30757 q = 1) (hb : d241832 q = 1) : d30757 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30981 q = 1) (hb : d241832 q = 1) : d30989 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d30981, d30989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30981, d30989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79081 (p : Pattern) (ha : d30995 p = 1) (hb : d241832 p = 1) : d243976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30977 q = 1) (hb : d241832 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30977, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79079 q ha hb
    | true =>
      simp only [d30977, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30978 q = 1) (hb : d241832 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30978, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30978, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30979 q = 1) (hb : d241832 q = 1) : d31328 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30979, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30979, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30980 q = 1) (hb : d241832 q = 1) : d31329 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30980, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30980, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30982 q = 1) (hb : d241832 q = 1) : d30990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30982, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79080 q ha hb
    | true =>
      simp only [d30982, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30983 q = 1) (hb : d241832 q = 1) : d30991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30983, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30983, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30984 q = 1) (hb : d241832 q = 1) : d30992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30984, d30992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30984, d30992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30985 q = 1) (hb : d241832 q = 1) : d30993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30985, d30993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30985, d30993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30986 q = 1) (hb : d241832 q = 1) : d31330 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30986, d31330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30986, d31330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30994 q = 1) (hb : d241832 q = 1) : d30994 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d30995 q = 1) (hb : d241832 q = 1) : d243976 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d30995, d243976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d30995, d243976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79082 (p : Pattern) (ha : d31005 p = 1) (hb : d241832 p = 1) : d243982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30996 q = 1) (hb : d241832 q = 1) : d243977 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30996, d243977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79081 q ha hb
    | true =>
      simp only [d30996, d243977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79043 q ha hb
  have h2 (q : Pattern) (ha : d30997 q = 1) (hb : d241832 q = 1) : d243978 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30997, d243978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30997, d243978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30998 q = 1) (hb : d241832 q = 1) : d243979 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30998, d243979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30998, d243979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30999 q = 1) (hb : d241832 q = 1) : d30999 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d31000 q = 1) (hb : d241832 q = 1) : d243829 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31000, d243829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79043 q ha hb
    | true =>
      simp only [d31000, d243829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31001 q = 1) (hb : d241832 q = 1) : d243830 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31001, d243830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31001, d243830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31002 q = 1) (hb : d241832 q = 1) : d243831 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31002, d243831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31002, d243831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31003 q = 1) (hb : d241832 q = 1) : d243980 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31003, d243980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31003, d243980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30765 q = 1) (hb : d241832 q = 1) : d243829 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30765, d243829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79043 q ha hb
    | true =>
      simp only [d30765, d243829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79025 q ha hb
  have h10 (q : Pattern) (ha : d30766 q = 1) (hb : d241832 q = 1) : d243830 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30766, d243830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30766, d243830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30767 q = 1) (hb : d241832 q = 1) : d243831 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30767, d243831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30767, d243831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d30 q = 1) (hb : d241832 q = 1) : d30 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d30645 q = 1) (hb : d241832 q = 1) : d243735 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30645, d243735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79025 q ha hb
    | true =>
      simp only [d30645, d243735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d30646 q = 1) (hb : d241832 q = 1) : d243736 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30646, d243736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30646, d243736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d30647 q = 1) (hb : d241832 q = 1) : d243737 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30647, d243737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30647, d243737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d30768 q = 1) (hb : d241832 q = 1) : d243832 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30768, d243832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30768, d243832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31004 q = 1) (hb : d241832 q = 1) : d243981 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31004, d243981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31004, d243981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d31005 q = 1) (hb : d241832 q = 1) : d243982 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31005, d243982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d31005, d243982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h18 p ha hb
theorem andIntro79083 (p : Pattern) (ha : d31011 p = 1) (hb : d241832 p = 1) : d243988 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31006 q = 1) (hb : d241832 q = 1) : d243983 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31006, d243983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79082 q ha hb
    | true =>
      simp only [d31006, d243983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31007 q = 1) (hb : d241832 q = 1) : d243984 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31007, d243984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31007, d243984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30916 q = 1) (hb : d241832 q = 1) : d243926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79061 q ha hb
    | true =>
      simp only [d30916, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30917 q = 1) (hb : d241832 q = 1) : d243927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31008 q = 1) (hb : d241832 q = 1) : d243985 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31008, d243985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31008, d243985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31009 q = 1) (hb : d241832 q = 1) : d243986 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31009, d243986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31009, d243986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31010 q = 1) (hb : d241832 q = 1) : d243987 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31010, d243987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31010, d243987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31011 q = 1) (hb : d241832 q = 1) : d243988 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31011, d243988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31011, d243988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79084 (p : Pattern) (ha : d31060 p = 1) (hb : d241832 p = 1) : d243994 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d241832 q = 1) : d243926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79061 q ha hb
    | true =>
      simp only [d30916, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d241832 q = 1) : d243927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31057 q = 1) (hb : d241832 q = 1) : d243991 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31057, d243991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31057, d243991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31058 q = 1) (hb : d241832 q = 1) : d243992 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31058, d243992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31058, d243992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31059 q = 1) (hb : d241832 q = 1) : d243993 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31059, d243993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31059, d243993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31060 q = 1) (hb : d241832 q = 1) : d243994 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31060, d243994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31060, d243994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79085 (p : Pattern) (ha : d241832 p = 1) (hb : d245431 p = 1) : d244000 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30953 q = 1) (hb : d241832 q = 1) : d243963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30953, d243963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79075 q ha hb
    | true =>
      simp only [d30953, d243963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79076 q ha hb
  have h2 (q : Pattern) (ha : d30954 q = 1) (hb : d241832 q = 1) : d243964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30954, d243964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30954, d243964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30955 q = 1) (hb : d241832 q = 1) : d243965 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30955, d243965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30955, d243965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30956 q = 1) (hb : d241832 q = 1) : d243966 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30956, d243966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30956, d243966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30963 q = 1) (hb : d241832 q = 1) : d243973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30963, d243973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79077 q ha hb
    | true =>
      simp only [d30963, d243973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79078 q ha hb
  have h6 (q : Pattern) (ha : d30964 q = 1) (hb : d241832 q = 1) : d243974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30964, d243974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30964, d243974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30965 q = 1) (hb : d241832 q = 1) : d243975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30965, d243975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30965, d243975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31012 q = 1) (hb : d241832 q = 1) : d243989 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31012, d243989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79083 q ha hb
    | true =>
      simp only [d31012, d243989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79063 q ha hb
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d245427 q = 1) : d243990 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245427, d243990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d245427, d243990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d31061 q = 1) (hb : d241832 q = 1) : d243995 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31061, d243995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79084 q ha hb
    | true =>
      simp only [d31061, d243995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31062 q = 1) (hb : d241832 q = 1) : d243996 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31062, d243996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31062, d243996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d241832 q = 1) (hb : d245428 q = 1) : d243997 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245428, d243997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245428, d243997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d241832 q = 1) (hb : d245429 q = 1) : d243998 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245429, d243998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d245429, d243998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d245430 q = 1) : d243999 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245430, d243999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d245430, d243999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d241832 q = 1) (hb : d245431 q = 1) : d244000 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245431, d244000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245431, d244000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79086 (p : Pattern) (ha : d31067 p = 1) (hb : d241832 p = 1) : d244001 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d241832 q = 1) : d243926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79061 q ha hb
    | true =>
      simp only [d30916, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d241832 q = 1) : d243927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30920 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79062 q ha hb
    | true =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30921 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30922 q = 1) (hb : d241832 q = 1) : d243932 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30922, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30922, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30923 q = 1) (hb : d241832 q = 1) : d243933 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30923, d243933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30923, d243933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30949 q = 1) (hb : d241832 q = 1) : d243959 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30949, d243959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30949, d243959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31067 q = 1) (hb : d241832 q = 1) : d244001 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31067, d244001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31067, d244001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79087 (p : Pattern) (ha : d31068 p = 1) (hb : d241832 p = 1) : d244002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30920 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79062 q ha hb
    | true =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30921 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30926 q = 1) (hb : d241832 q = 1) : d243936 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30926, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30926, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30927 q = 1) (hb : d241832 q = 1) : d243937 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30927, d243937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30927, d243937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30951 q = 1) (hb : d241832 q = 1) : d243961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30951, d243961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30951, d243961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31068 q = 1) (hb : d241832 q = 1) : d244002 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31068, d244002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31068, d244002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79088 (p : Pattern) (ha : d31073 p = 1) (hb : d241832 p = 1) : d244007 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d241832 q = 1) : d243926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79061 q ha hb
    | true =>
      simp only [d30916, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d241832 q = 1) : d243927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30920 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79062 q ha hb
    | true =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30921 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30922 q = 1) (hb : d241832 q = 1) : d243932 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30922, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30922, d243932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30957 q = 1) (hb : d241832 q = 1) : d243967 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30957, d243967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30957, d243967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30958 q = 1) (hb : d241832 q = 1) : d243968 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30958, d243968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30958, d243968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31073 q = 1) (hb : d241832 q = 1) : d244007 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31073, d244007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31073, d244007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79089 (p : Pattern) (ha : d31074 p = 1) (hb : d241832 p = 1) : d244008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30920 q = 1) (hb : d241832 q = 1) : d243930 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79062 q ha hb
    | true =>
      simp only [d30920, d243930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30921 q = 1) (hb : d241832 q = 1) : d243931 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30921, d243931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30926 q = 1) (hb : d241832 q = 1) : d243936 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d30926, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30926, d243936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30960 q = 1) (hb : d241832 q = 1) : d243970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d30960, d243970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30960, d243970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30961 q = 1) (hb : d241832 q = 1) : d243971 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d30961, d243971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30961, d243971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31074 q = 1) (hb : d241832 q = 1) : d244008 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31074, d244008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31074, d244008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79090 (p : Pattern) (ha : d31078 p = 1) (hb : d241832 p = 1) : d244012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31006 q = 1) (hb : d241832 q = 1) : d243983 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31006, d243983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79082 q ha hb
    | true =>
      simp only [d31006, d243983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31007 q = 1) (hb : d241832 q = 1) : d243984 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31007, d243984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31007, d243984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30916 q = 1) (hb : d241832 q = 1) : d243926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79061 q ha hb
    | true =>
      simp only [d30916, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30917 q = 1) (hb : d241832 q = 1) : d243927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31008 q = 1) (hb : d241832 q = 1) : d243985 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31008, d243985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31008, d243985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31009 q = 1) (hb : d241832 q = 1) : d243986 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31009, d243986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31009, d243986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31010 q = 1) (hb : d241832 q = 1) : d243987 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31010, d243987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31010, d243987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31078 q = 1) (hb : d241832 q = 1) : d244012 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31078, d244012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31078, d244012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79091 (p : Pattern) (ha : d31084 p = 1) (hb : d241832 p = 1) : d244015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30916 q = 1) (hb : d241832 q = 1) : d243926 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d30916, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79061 q ha hb
    | true =>
      simp only [d30916, d243926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30917 q = 1) (hb : d241832 q = 1) : d243927 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d30917, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30917, d243927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31057 q = 1) (hb : d241832 q = 1) : d243991 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31057, d243991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31057, d243991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31058 q = 1) (hb : d241832 q = 1) : d243992 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31058, d243992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31058, d243992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31059 q = 1) (hb : d241832 q = 1) : d243993 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31059, d243993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31059, d243993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31084 q = 1) (hb : d241832 q = 1) : d244015 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31084, d244015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31084, d244015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79092 (p : Pattern) (ha : d241832 p = 1) (hb : d245436 p = 1) : d244021 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30953 q = 1) (hb : d241832 q = 1) : d243963 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30953, d243963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79075 q ha hb
    | true =>
      simp only [d30953, d243963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79076 q ha hb
  have h2 (q : Pattern) (ha : d30954 q = 1) (hb : d241832 q = 1) : d243964 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30954, d243964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30954, d243964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30955 q = 1) (hb : d241832 q = 1) : d243965 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30955, d243965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30955, d243965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d30956 q = 1) (hb : d241832 q = 1) : d243966 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d30956, d243966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30956, d243966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30963 q = 1) (hb : d241832 q = 1) : d243973 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d30963, d243973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79077 q ha hb
    | true =>
      simp only [d30963, d243973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79078 q ha hb
  have h6 (q : Pattern) (ha : d30964 q = 1) (hb : d241832 q = 1) : d243974 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d30964, d243974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30964, d243974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30965 q = 1) (hb : d241832 q = 1) : d243975 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d30965, d243975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d30965, d243975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31012 q = 1) (hb : d241832 q = 1) : d243989 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31012, d243989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79083 q ha hb
    | true =>
      simp only [d31012, d243989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79063 q ha hb
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d245427 q = 1) : d243990 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245427, d243990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d245427, d243990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d31061 q = 1) (hb : d241832 q = 1) : d243995 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31061, d243995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79084 q ha hb
    | true =>
      simp only [d31061, d243995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31062 q = 1) (hb : d241832 q = 1) : d243996 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31062, d243996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31062, d243996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d241832 q = 1) (hb : d245428 q = 1) : d243997 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245428, d243997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245428, d243997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d241832 q = 1) (hb : d245429 q = 1) : d243998 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245429, d243998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d245429, d243998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d245430 q = 1) : d243999 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245430, d243999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d245430, d243999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d31069 q = 1) (hb : d241832 q = 1) : d244003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31069, d244003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79086 q ha hb
    | true =>
      simp only [d31069, d244003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79087 q ha hb
  have h16 (q : Pattern) (ha : d31070 q = 1) (hb : d241832 q = 1) : d244004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31070, d244004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31070, d244004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31071 q = 1) (hb : d241832 q = 1) : d244005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31071, d244005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31071, d244005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31072 q = 1) (hb : d241832 q = 1) : d244006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31072, d244006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31072, d244006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31075 q = 1) (hb : d241832 q = 1) : d244009 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31075, d244009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79088 q ha hb
    | true =>
      simp only [d31075, d244009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79089 q ha hb
  have h20 (q : Pattern) (ha : d31076 q = 1) (hb : d241832 q = 1) : d244010 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31076, d244010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31076, d244010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d31077 q = 1) (hb : d241832 q = 1) : d244011 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31077, d244011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d31077, d244011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d31079 q = 1) (hb : d241832 q = 1) : d244013 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31079, d244013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79090 q ha hb
    | true =>
      simp only [d31079, d244013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79066 q ha hb
  have h23 (q : Pattern) (ha : d241832 q = 1) (hb : d245432 q = 1) : d244014 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245432, d244014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d245432, d244014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d31085 q = 1) (hb : d241832 q = 1) : d244016 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31085, d244016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79091 q ha hb
    | true =>
      simp only [d31085, d244016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d31086 q = 1) (hb : d241832 q = 1) : d244017 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31086, d244017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d31086, d244017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d241832 q = 1) (hb : d245433 q = 1) : d244018 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245433, d244018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d245433, d244018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d241832 q = 1) (hb : d245434 q = 1) : d244019 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245434, d244019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d245434, d244019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d241832 q = 1) (hb : d245435 q = 1) : d244020 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245435, d244020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d245435, d244020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d241832 q = 1) (hb : d245436 q = 1) : d244021 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245436, d244021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245436, d244021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro79093 (p : Pattern) (ha : d241832 p = 1) (hb : d245443 p = 1) : d244041 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31079 q = 1) (hb : d241832 q = 1) : d244013 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31079, d244013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79090 q ha hb
    | true =>
      simp only [d31079, d244013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79066 q ha hb
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d245432 q = 1) : d244014 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245432, d244014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245432, d244014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d31085 q = 1) (hb : d241832 q = 1) : d244016 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31085, d244016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79091 q ha hb
    | true =>
      simp only [d31085, d244016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31086 q = 1) (hb : d241832 q = 1) : d244017 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31086, d244017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31086, d244017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d245433 q = 1) : d244018 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245433, d244018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245433, d244018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d245441 q = 1) : d244039 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245441, d244039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245441, d244039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d245442 q = 1) : d244040 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245442, d244040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245442, d244040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d245443 q = 1) : d244041 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245443, d244041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245443, d244041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79094 (p : Pattern) (ha : d31132 p = 1) (hb : d241832 p = 1) : d244049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31118 q = 1) (hb : d241832 q = 1) : d31484 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31118, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31118, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79079 q ha hb
  have h2 (q : Pattern) (ha : d30977 q = 1) (hb : d241832 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30977, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79079 q ha hb
    | true =>
      simp only [d30977, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31119 q = 1) (hb : d241832 q = 1) : d31485 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31119, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31119, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30978 q = 1) (hb : d241832 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30978, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30978, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31120 q = 1) (hb : d241832 q = 1) : d31486 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31120, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31120, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31121 q = 1) (hb : d241832 q = 1) : d31487 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31121, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31121, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31122 q = 1) (hb : d241832 q = 1) : d31127 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31122, d31127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31122, d31127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79080 q ha hb
  have h8 (q : Pattern) (ha : d30982 q = 1) (hb : d241832 q = 1) : d30990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30982, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79080 q ha hb
    | true =>
      simp only [d30982, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31123 q = 1) (hb : d241832 q = 1) : d31128 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31123, d31128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31123, d31128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30983 q = 1) (hb : d241832 q = 1) : d30991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30983, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30983, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31124 q = 1) (hb : d241832 q = 1) : d31129 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31124, d31129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31124, d31129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31125 q = 1) (hb : d241832 q = 1) : d31130 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31125, d31130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31125, d31130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31126 q = 1) (hb : d241832 q = 1) : d31488 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31126, d31488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31126, d31488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31131 q = 1) (hb : d241832 q = 1) : d31131 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d31132 q = 1) (hb : d241832 q = 1) : d244049 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31132, d244049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31132, d244049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79095 (p : Pattern) (ha : d31142 p = 1) (hb : d241832 p = 1) : d244055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31133 q = 1) (hb : d241832 q = 1) : d244050 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31133, d244050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79094 q ha hb
    | true =>
      simp only [d31133, d244050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79054 q ha hb
  have h2 (q : Pattern) (ha : d31134 q = 1) (hb : d241832 q = 1) : d244051 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31134, d244051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31134, d244051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31135 q = 1) (hb : d241832 q = 1) : d244052 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31135, d244052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31135, d244052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31136 q = 1) (hb : d241832 q = 1) : d31136 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d31137 q = 1) (hb : d241832 q = 1) : d243887 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31137, d243887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79054 q ha hb
    | true =>
      simp only [d31137, d243887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31138 q = 1) (hb : d241832 q = 1) : d243888 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31138, d243888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31138, d243888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31139 q = 1) (hb : d241832 q = 1) : d243889 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31139, d243889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31139, d243889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31140 q = 1) (hb : d241832 q = 1) : d244053 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31140, d244053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31140, d244053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d30858 q = 1) (hb : d241832 q = 1) : d243887 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30858, d243887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79054 q ha hb
    | true =>
      simp only [d30858, d243887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79032 q ha hb
  have h10 (q : Pattern) (ha : d30859 q = 1) (hb : d241832 q = 1) : d243888 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30859, d243888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30859, d243888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d30860 q = 1) (hb : d241832 q = 1) : d243889 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30860, d243889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30860, d243889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d71 q = 1) (hb : d241832 q = 1) : d71 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d30688 q = 1) (hb : d241832 q = 1) : d243772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30688, d243772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79032 q ha hb
    | true =>
      simp only [d30688, d243772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d30689 q = 1) (hb : d241832 q = 1) : d243773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30689, d243773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30689, d243773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d30690 q = 1) (hb : d241832 q = 1) : d243774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30690, d243774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30690, d243774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d30861 q = 1) (hb : d241832 q = 1) : d243890 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30861, d243890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d30861, d243890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31141 q = 1) (hb : d241832 q = 1) : d244054 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31141, d244054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31141, d244054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d31142 q = 1) (hb : d241832 q = 1) : d244055 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31142, d244055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d31142, d244055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h18 p ha hb
theorem andIntro79096 (p : Pattern) (ha : d31147 p = 1) (hb : d241832 p = 1) : d244060 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30858 q = 1) (hb : d241832 q = 1) : d243887 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30858, d243887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79054 q ha hb
    | true =>
      simp only [d30858, d243887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79032 q ha hb
  have h2 (q : Pattern) (ha : d30859 q = 1) (hb : d241832 q = 1) : d243888 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30859, d243888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30859, d243888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d30860 q = 1) (hb : d241832 q = 1) : d243889 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30860, d243889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30860, d243889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71 q = 1) (hb : d241832 q = 1) : d71 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d30688 q = 1) (hb : d241832 q = 1) : d243772 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d30688, d243772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79032 q ha hb
    | true =>
      simp only [d30688, d243772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30689 q = 1) (hb : d241832 q = 1) : d243773 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d30689, d243773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30689, d243773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d30690 q = 1) (hb : d241832 q = 1) : d243774 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d30690, d243774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30690, d243774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30861 q = 1) (hb : d241832 q = 1) : d243890 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d30861, d243890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30861, d243890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d31145 q = 1) (hb : d241832 q = 1) : d244058 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31145, d244058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31145, d244058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d31146 q = 1) (hb : d241832 q = 1) : d244059 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31146, d244059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31146, d244059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31147 q = 1) (hb : d241832 q = 1) : d244060 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31147, d244060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31147, d244060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h11 p ha hb
theorem andIntro79097 (p : Pattern) (ha : d31153 p = 1) (hb : d241832 p = 1) : d244066 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31143 q = 1) (hb : d241832 q = 1) : d244056 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31143, d244056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79095 q ha hb
    | true =>
      simp only [d31143, d244056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31144 q = 1) (hb : d241832 q = 1) : d244057 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31144, d244057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31144, d244057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31148 q = 1) (hb : d241832 q = 1) : d244061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31148, d244061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79096 q ha hb
    | true =>
      simp only [d31148, d244061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31149 q = 1) (hb : d241832 q = 1) : d244062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31149, d244062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31149, d244062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31150 q = 1) (hb : d241832 q = 1) : d244063 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31150, d244063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31150, d244063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31151 q = 1) (hb : d241832 q = 1) : d244064 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31151, d244064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31151, d244064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31152 q = 1) (hb : d241832 q = 1) : d244065 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31152, d244065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31152, d244065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31153 q = 1) (hb : d241832 q = 1) : d244066 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31153, d244066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31153, d244066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79098 (p : Pattern) (ha : d31161 p = 1) (hb : d241832 p = 1) : d244074 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31148 q = 1) (hb : d241832 q = 1) : d244061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31148, d244061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79096 q ha hb
    | true =>
      simp only [d31148, d244061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31149 q = 1) (hb : d241832 q = 1) : d244062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31149, d244062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31149, d244062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31156 q = 1) (hb : d241832 q = 1) : d244069 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31156, d244069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79072 q ha hb
    | true =>
      simp only [d31156, d244069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31157 q = 1) (hb : d241832 q = 1) : d244070 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31157, d244070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31157, d244070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31158 q = 1) (hb : d241832 q = 1) : d244071 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31158, d244071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31158, d244071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31159 q = 1) (hb : d241832 q = 1) : d244072 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31159, d244072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31159, d244072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31160 q = 1) (hb : d241832 q = 1) : d244073 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31160, d244073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31160, d244073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31161 q = 1) (hb : d241832 q = 1) : d244074 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31161, d244074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31161, d244074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79099 (p : Pattern) (ha : d31200 p = 1) (hb : d241832 p = 1) : d244080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31148 q = 1) (hb : d241832 q = 1) : d244061 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31148, d244061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79096 q ha hb
    | true =>
      simp only [d31148, d244061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31149 q = 1) (hb : d241832 q = 1) : d244062 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31149, d244062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31149, d244062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31197 q = 1) (hb : d241832 q = 1) : d244077 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31197, d244077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31197, d244077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31198 q = 1) (hb : d241832 q = 1) : d244078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31198, d244078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31198, d244078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31199 q = 1) (hb : d241832 q = 1) : d244079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31199, d244079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31199, d244079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31200 q = 1) (hb : d241832 q = 1) : d244080 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31200, d244080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31200, d244080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79100 (p : Pattern) (ha : d241832 p = 1) (hb : d245453 p = 1) : d244086 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31162 q = 1) (hb : d241832 q = 1) : d244075 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31162, d244075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79097 q ha hb
    | true =>
      simp only [d31162, d244075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79098 q ha hb
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d245449 q = 1) : d244076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245449, d244076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245449, d244076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d31201 q = 1) (hb : d241832 q = 1) : d244081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31201, d244081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79099 q ha hb
    | true =>
      simp only [d31201, d244081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31202 q = 1) (hb : d241832 q = 1) : d244082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31202, d244082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31202, d244082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d245450 q = 1) : d244083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245450, d244083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245450, d244083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d245451 q = 1) : d244084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245451, d244084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245451, d244084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d245452 q = 1) : d244085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245452, d244085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245452, d244085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d245453 q = 1) : d244086 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245453, d244086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245453, d244086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79101 (p : Pattern) (ha : d241832 p = 1) (hb : d245459 p = 1) : d244103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30936 q = 1) (hb : d241832 q = 1) : d243946 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30936, d243946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30936, d243946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79065 q ha hb
  have h2 (q : Pattern) (ha : d30937 q = 1) (hb : d241832 q = 1) : d243947 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30937, d243947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30937, d243947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30946 q = 1) (hb : d241832 q = 1) : d243956 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d30946, d243956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79065 q ha hb
    | true =>
      simp only [d30946, d243956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79068 q ha hb
  have h4 (q : Pattern) (ha : d30947 q = 1) (hb : d241832 q = 1) : d243957 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d30947, d243957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30947, d243957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30948 q = 1) (hb : d241832 q = 1) : d243958 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d30948, d243958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30948, d243958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d245437 q = 1) : d244022 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245437, d244022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79085 q ha hb
    | true =>
      simp only [d245437, d244022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79092 q ha hb
  have h7 (q : Pattern) (ha : d31104 q = 1) (hb : d241832 q = 1) : d244035 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31104, d244035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79069 q ha hb
    | true =>
      simp only [d31104, d244035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79070 q ha hb
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d245438 q = 1) : d244036 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245438, d244036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245438, d244036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d245439 q = 1) : d244037 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245439, d244037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245439, d244037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d241832 q = 1) (hb : d245440 q = 1) : d244038 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245440, d244038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d245440, d244038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d241832 q = 1) (hb : d245444 q = 1) : d244042 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245444, d244042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245444, d244042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79093 q ha hb
  have h12 (q : Pattern) (ha : d31113 q = 1) (hb : d241832 q = 1) : d244044 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31113, d244044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31113, d244044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79071 q ha hb
  have h13 (q : Pattern) (ha : d241832 q = 1) (hb : d245445 q = 1) : d244045 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245445, d244045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245445, d244045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d245446 q = 1) : d244046 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245446, d244046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245446, d244046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d241832 q = 1) (hb : d245447 q = 1) : d244047 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245447, d244047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245447, d244047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d241832 q = 1) (hb : d245448 q = 1) : d244048 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245448, d244048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245448, d244048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d241832 q = 1) (hb : d245454 q = 1) : d244087 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245454, d244087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245454, d244087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79100 q ha hb
  have h18 (q : Pattern) (ha : d31218 q = 1) (hb : d241832 q = 1) : d244098 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31218, d244098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31218, d244098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79074 q ha hb
  have h19 (q : Pattern) (ha : d241832 q = 1) (hb : d245455 q = 1) : d244099 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245455, d244099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245455, d244099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d241832 q = 1) (hb : d245456 q = 1) : d244100 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245456, d244100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d245456, d244100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d241832 q = 1) (hb : d245457 q = 1) : d244101 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245457, d244101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d245457, d244101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d241832 q = 1) (hb : d245458 q = 1) : d244102 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245458, d244102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245458, d244102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d241832 q = 1) (hb : d245459 q = 1) : d244103 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245459, d244103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245459, d244103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro79102 (p : Pattern) (ha : d241832 p = 1) (hb : d245465 p = 1) : d244109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d245460 q = 1) : d244104 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245460, d244104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245460, d244104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79101 q ha hb
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d245461 q = 1) : d244105 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245461, d244105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245461, d244105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d245462 q = 1) : d244106 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245462, d244106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245462, d244106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d245463 q = 1) : d244107 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245463, d244107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245463, d244107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d245464 q = 1) : d244108 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245464, d244108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245464, d244108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d245465 q = 1) : d244109 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245465, d244109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245465, d244109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79103 (p : Pattern) (ha : d31231 p = 1) (hb : d241832 p = 1) : d244111 p = 1 := by
  have h0 (q : Pattern) (ha : d30635 q = 1) (hb : d241831 q = 1) : d30635 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30636 q = 1) (hb : d241832 q = 1) : d30756 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30636, d241832, d30756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30636, d241832, d30756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30637 q = 1) (hb : d241832 q = 1) : d30757 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30637, d30757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30637, d30757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31231 q = 1) (hb : d241832 q = 1) : d244111 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31231, d244111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31231, d244111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro79104 (p : Pattern) (ha : d31237 p = 1) (hb : d241832 p = 1) : d244117 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30977 q = 1) (hb : d241832 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30977, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79079 q ha hb
    | true =>
      simp only [d30977, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30978 q = 1) (hb : d241832 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30978, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30978, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30979 q = 1) (hb : d241832 q = 1) : d31328 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30979, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30979, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30980 q = 1) (hb : d241832 q = 1) : d31329 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30980, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30980, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30982 q = 1) (hb : d241832 q = 1) : d30990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30982, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79080 q ha hb
    | true =>
      simp only [d30982, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d30983 q = 1) (hb : d241832 q = 1) : d30991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30983, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30983, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d30984 q = 1) (hb : d241832 q = 1) : d30992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30984, d30992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30984, d30992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d30985 q = 1) (hb : d241832 q = 1) : d30993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30985, d30993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d30985, d30993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d30986 q = 1) (hb : d241832 q = 1) : d31330 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d30986, d31330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d30986, d31330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30993 q = 1) (hb : d241832 q = 1) : d30993 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d31232 q = 1) (hb : d241832 q = 1) : d244112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79103 q ha hb
    | true =>
      simp only [d31232, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d31233 q = 1) (hb : d241832 q = 1) : d244113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31233, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31234 q = 1) (hb : d241832 q = 1) : d244114 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31234, d244114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31234, d244114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31235 q = 1) (hb : d241832 q = 1) : d244115 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31235, d244115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31235, d244115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31236 q = 1) (hb : d241832 q = 1) : d244116 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31236, d244116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31236, d244116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d31237 q = 1) (hb : d241832 q = 1) : d244117 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31237, d244117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31237, d244117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro79105 (p : Pattern) (ha : d31240 p = 1) (hb : d241832 p = 1) : d244119 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30751 q = 1) (hb : d241832 q = 1) : d30990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30751, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79042 q ha hb
    | true =>
      simp only [d30751, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d30752 q = 1) (hb : d241832 q = 1) : d30991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30752, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30752, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30753 q = 1) (hb : d241832 q = 1) : d30992 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30753, d30992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30753, d30992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30754 q = 1) (hb : d241832 q = 1) : d30993 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30754, d30993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30754, d30993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31232 q = 1) (hb : d241832 q = 1) : d244112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79103 q ha hb
    | true =>
      simp only [d31232, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31233 q = 1) (hb : d241832 q = 1) : d244113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31233, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31234 q = 1) (hb : d241832 q = 1) : d244114 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31234, d244114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31234, d244114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31235 q = 1) (hb : d241832 q = 1) : d244115 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31235, d244115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31235, d244115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31238 q = 1) (hb : d241832 q = 1) : d244116 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31238, d244116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31238, d244116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31239 q = 1) (hb : d241832 q = 1) : d244118 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31239, d244118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31239, d244118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31240 q = 1) (hb : d241832 q = 1) : d244119 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31240, d244119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31240, d244119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79106 (p : Pattern) (ha : d31244 p = 1) (hb : d241832 p = 1) : d244123 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31232 q = 1) (hb : d241832 q = 1) : d244112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79103 q ha hb
    | true =>
      simp only [d31232, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31233 q = 1) (hb : d241832 q = 1) : d244113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31233, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31234 q = 1) (hb : d241832 q = 1) : d244114 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31234, d244114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31234, d244114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31235 q = 1) (hb : d241832 q = 1) : d244115 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31235, d244115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31235, d244115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31239 q = 1) (hb : d241832 q = 1) : d244118 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31239, d244118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31239, d244118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31244 q = 1) (hb : d241832 q = 1) : d244123 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31244, d244123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31244, d244123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79107 (p : Pattern) (ha : d31251 p = 1) (hb : d241832 p = 1) : d244130 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31241 q = 1) (hb : d241832 q = 1) : d244120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31241, d244120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79104 q ha hb
    | true =>
      simp only [d31241, d244120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79105 q ha hb
  have h2 (q : Pattern) (ha : d31242 q = 1) (hb : d241832 q = 1) : d244121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31242, d244121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31242, d244121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31243 q = 1) (hb : d241832 q = 1) : d244122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31243, d244122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31243, d244122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31245 q = 1) (hb : d241832 q = 1) : d244124 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31245, d244124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79105 q ha hb
    | true =>
      simp only [d31245, d244124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79106 q ha hb
  have h5 (q : Pattern) (ha : d31246 q = 1) (hb : d241832 q = 1) : d244125 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31246, d244125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31246, d244125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31247 q = 1) (hb : d241832 q = 1) : d244126 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31247, d244126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31247, d244126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31248 q = 1) (hb : d241832 q = 1) : d244127 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31248, d244127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31248, d244127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31249 q = 1) (hb : d241832 q = 1) : d244128 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31249, d244128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31249, d244128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31250 q = 1) (hb : d241832 q = 1) : d244129 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31250, d244129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31250, d244129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31251 q = 1) (hb : d241832 q = 1) : d244130 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31251, d244130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31251, d244130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro79108 (p : Pattern) (ha : d31255 p = 1) (hb : d241832 p = 1) : d244134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31245 q = 1) (hb : d241832 q = 1) : d244124 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31245, d244124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79105 q ha hb
    | true =>
      simp only [d31245, d244124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79106 q ha hb
  have h2 (q : Pattern) (ha : d31246 q = 1) (hb : d241832 q = 1) : d244125 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31246, d244125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31246, d244125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31247 q = 1) (hb : d241832 q = 1) : d244126 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31247, d244126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31247, d244126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31249 q = 1) (hb : d241832 q = 1) : d244128 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31249, d244128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31249, d244128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31254 q = 1) (hb : d241832 q = 1) : d244133 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31254, d244133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31254, d244133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31255 q = 1) (hb : d241832 q = 1) : d244134 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31255, d244134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31255, d244134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79109 (p : Pattern) (ha : d31261 p = 1) (hb : d241832 p = 1) : d244140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31252 q = 1) (hb : d241832 q = 1) : d244131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79107 q ha hb
    | true =>
      simp only [d31252, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31253 q = 1) (hb : d241832 q = 1) : d244132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31256 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79108 q ha hb
    | true =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31257 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31258 q = 1) (hb : d241832 q = 1) : d244137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31258, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31258, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31259 q = 1) (hb : d241832 q = 1) : d244138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31259, d244138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31259, d244138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31260 q = 1) (hb : d241832 q = 1) : d244139 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31260, d244139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31260, d244139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31261 q = 1) (hb : d241832 q = 1) : d244140 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31261, d244140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31261, d244140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79110 (p : Pattern) (ha : d31265 p = 1) (hb : d241832 p = 1) : d244144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31256 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79108 q ha hb
    | true =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31257 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31262 q = 1) (hb : d241832 q = 1) : d244141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31262, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31262, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31263 q = 1) (hb : d241832 q = 1) : d244142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31263, d244142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31263, d244142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31264 q = 1) (hb : d241832 q = 1) : d244143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31264, d244143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31264, d244143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31265 q = 1) (hb : d241832 q = 1) : d244144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31265, d244144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31265, d244144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79111 (p : Pattern) (ha : d31271 p = 1) (hb : d241832 p = 1) : d244150 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31266 q = 1) (hb : d241832 q = 1) : d244145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31266, d244145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79109 q ha hb
    | true =>
      simp only [d31266, d244145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79110 q ha hb
  have h2 (q : Pattern) (ha : d31267 q = 1) (hb : d241832 q = 1) : d244146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31267, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31267, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31268 q = 1) (hb : d241832 q = 1) : d244147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31268, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31268, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31269 q = 1) (hb : d241832 q = 1) : d244148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31269, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31269, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31270 q = 1) (hb : d241832 q = 1) : d244149 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31270, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31270, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31271 q = 1) (hb : d241832 q = 1) : d244150 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31271, d244150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31271, d244150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79112 (p : Pattern) (ha : d31274 p = 1) (hb : d241832 p = 1) : d244153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31252 q = 1) (hb : d241832 q = 1) : d244131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79107 q ha hb
    | true =>
      simp only [d31252, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31253 q = 1) (hb : d241832 q = 1) : d244132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31256 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79108 q ha hb
    | true =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31257 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31258 q = 1) (hb : d241832 q = 1) : d244137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31258, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31258, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31259 q = 1) (hb : d241832 q = 1) : d244138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31259, d244138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31259, d244138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31260 q = 1) (hb : d241832 q = 1) : d244139 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31260, d244139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31260, d244139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31274 q = 1) (hb : d241832 q = 1) : d244153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31274, d244153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31274, d244153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79113 (p : Pattern) (ha : d31275 p = 1) (hb : d241832 p = 1) : d244154 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31256 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79108 q ha hb
    | true =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31257 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31262 q = 1) (hb : d241832 q = 1) : d244141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31262, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31262, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31263 q = 1) (hb : d241832 q = 1) : d244142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31263, d244142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31263, d244142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31264 q = 1) (hb : d241832 q = 1) : d244143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31264, d244143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31264, d244143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31275 q = 1) (hb : d241832 q = 1) : d244154 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31275, d244154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31275, d244154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79114 (p : Pattern) (ha : d31281 p = 1) (hb : d241832 p = 1) : d244160 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31266 q = 1) (hb : d241832 q = 1) : d244145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31266, d244145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79109 q ha hb
    | true =>
      simp only [d31266, d244145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79110 q ha hb
  have h2 (q : Pattern) (ha : d31267 q = 1) (hb : d241832 q = 1) : d244146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31267, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31267, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31268 q = 1) (hb : d241832 q = 1) : d244147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31268, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31268, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31269 q = 1) (hb : d241832 q = 1) : d244148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31269, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31269, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31270 q = 1) (hb : d241832 q = 1) : d244149 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31270, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31270, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31276 q = 1) (hb : d241832 q = 1) : d244155 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31276, d244155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79112 q ha hb
    | true =>
      simp only [d31276, d244155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79113 q ha hb
  have h7 (q : Pattern) (ha : d31277 q = 1) (hb : d241832 q = 1) : d244156 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31277, d244156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31277, d244156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31278 q = 1) (hb : d241832 q = 1) : d244157 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31278, d244157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31278, d244157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31279 q = 1) (hb : d241832 q = 1) : d244158 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31279, d244158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31279, d244158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31280 q = 1) (hb : d241832 q = 1) : d244159 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31280, d244159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31280, d244159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31281 q = 1) (hb : d241832 q = 1) : d244160 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31281, d244160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31281, d244160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79115 (p : Pattern) (ha : d31454 p = 1) (hb : d241832 p = 1) : d244234 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31266 q = 1) (hb : d241832 q = 1) : d244145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31266, d244145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79109 q ha hb
    | true =>
      simp only [d31266, d244145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79110 q ha hb
  have h2 (q : Pattern) (ha : d31267 q = 1) (hb : d241832 q = 1) : d244146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31267, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31267, d244146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31268 q = 1) (hb : d241832 q = 1) : d244147 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31268, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31268, d244147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31269 q = 1) (hb : d241832 q = 1) : d244148 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31269, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31269, d244148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31270 q = 1) (hb : d241832 q = 1) : d244149 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31270, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31270, d244149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31449 q = 1) (hb : d241832 q = 1) : d244229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31449, d244229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79110 q ha hb
    | true =>
      simp only [d31449, d244229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31450 q = 1) (hb : d241832 q = 1) : d244230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31450, d244230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31450, d244230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31451 q = 1) (hb : d241832 q = 1) : d244231 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31451, d244231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31451, d244231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31452 q = 1) (hb : d241832 q = 1) : d244232 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31452, d244232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31452, d244232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31453 q = 1) (hb : d241832 q = 1) : d244233 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31453, d244233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31453, d244233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31454 q = 1) (hb : d241832 q = 1) : d244234 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31454, d244234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31454, d244234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79116 (p : Pattern) (ha : d31460 p = 1) (hb : d241832 p = 1) : d244240 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31449 q = 1) (hb : d241832 q = 1) : d244229 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31449, d244229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79110 q ha hb
    | true =>
      simp only [d31449, d244229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31450 q = 1) (hb : d241832 q = 1) : d244230 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31450, d244230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31450, d244230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31451 q = 1) (hb : d241832 q = 1) : d244231 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31451, d244231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31451, d244231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31452 q = 1) (hb : d241832 q = 1) : d244232 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31452, d244232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31452, d244232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31453 q = 1) (hb : d241832 q = 1) : d244233 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31453, d244233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31453, d244233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31455 q = 1) (hb : d241832 q = 1) : d244235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31455, d244235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79113 q ha hb
    | true =>
      simp only [d31455, d244235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31456 q = 1) (hb : d241832 q = 1) : d244236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31456, d244236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31456, d244236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31457 q = 1) (hb : d241832 q = 1) : d244237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31457, d244237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31457, d244237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31458 q = 1) (hb : d241832 q = 1) : d244238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31458, d244238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31458, d244238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31459 q = 1) (hb : d241832 q = 1) : d244239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31459, d244239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31459, d244239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31460 q = 1) (hb : d241832 q = 1) : d244240 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31460, d244240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31460, d244240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79117 (p : Pattern) (ha : d31469 p = 1) (hb : d241832 p = 1) : d244249 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31455 q = 1) (hb : d241832 q = 1) : d244235 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31455, d244235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79113 q ha hb
    | true =>
      simp only [d31455, d244235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31456 q = 1) (hb : d241832 q = 1) : d244236 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31456, d244236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31456, d244236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31457 q = 1) (hb : d241832 q = 1) : d244237 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31457, d244237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31457, d244237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31458 q = 1) (hb : d241832 q = 1) : d244238 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31458, d244238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31458, d244238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31459 q = 1) (hb : d241832 q = 1) : d244239 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31459, d244239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31459, d244239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31469 q = 1) (hb : d241832 q = 1) : d244249 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31469, d244249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31469, d244249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79118 (p : Pattern) (ha : d31506 p = 1) (hb : d241832 p = 1) : d244267 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30847 q = 1) (hb : d241832 q = 1) : d31127 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30847, d31127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30847, d31127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79042 q ha hb
  have h2 (q : Pattern) (ha : d30751 q = 1) (hb : d241832 q = 1) : d30990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30751, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79042 q ha hb
    | true =>
      simp only [d30751, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d30848 q = 1) (hb : d241832 q = 1) : d31128 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30848, d31128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d30848, d31128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30752 q = 1) (hb : d241832 q = 1) : d30991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30752, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30752, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d30849 q = 1) (hb : d241832 q = 1) : d31129 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d30849, d31129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d30849, d31129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d30850 q = 1) (hb : d241832 q = 1) : d31130 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d30850, d31130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d30850, d31130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31490 q = 1) (hb : d241832 q = 1) : d244257 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31490, d244257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31490, d244257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79103 q ha hb
  have h8 (q : Pattern) (ha : d31232 q = 1) (hb : d241832 q = 1) : d244112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79103 q ha hb
    | true =>
      simp only [d31232, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31491 q = 1) (hb : d241832 q = 1) : d244258 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31491, d244258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31491, d244258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31233 q = 1) (hb : d241832 q = 1) : d244113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31233, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31492 q = 1) (hb : d241832 q = 1) : d244259 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31492, d244259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31492, d244259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31493 q = 1) (hb : d241832 q = 1) : d244260 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31493, d244260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31493, d244260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31505 q = 1) (hb : d241832 q = 1) : d244261 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31505, d244261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31505, d244261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31499 q = 1) (hb : d241832 q = 1) : d244266 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31499, d244266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31499, d244266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31506 q = 1) (hb : d241832 q = 1) : d244267 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31506, d244267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31506, d244267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79119 (p : Pattern) (ha : d31510 p = 1) (hb : d241832 p = 1) : d244272 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31490 q = 1) (hb : d241832 q = 1) : d244257 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31490, d244257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31490, d244257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79103 q ha hb
  have h2 (q : Pattern) (ha : d31232 q = 1) (hb : d241832 q = 1) : d244112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79103 q ha hb
    | true =>
      simp only [d31232, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31491 q = 1) (hb : d241832 q = 1) : d244258 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31491, d244258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31491, d244258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31233 q = 1) (hb : d241832 q = 1) : d244113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31233, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31492 q = 1) (hb : d241832 q = 1) : d244259 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31492, d244259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31492, d244259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31493 q = 1) (hb : d241832 q = 1) : d244260 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31493, d244260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31493, d244260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31499 q = 1) (hb : d241832 q = 1) : d244266 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31499, d244266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31499, d244266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31510 q = 1) (hb : d241832 q = 1) : d244272 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31510, d244272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31510, d244272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79120 (p : Pattern) (ha : d31529 p = 1) (hb : d241832 p = 1) : d244291 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31511 q = 1) (hb : d241832 q = 1) : d244273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31511, d244273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79118 q ha hb
    | true =>
      simp only [d31511, d244273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79119 q ha hb
  have h2 (q : Pattern) (ha : d31512 q = 1) (hb : d241832 q = 1) : d244274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31512, d244274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31512, d244274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31513 q = 1) (hb : d241832 q = 1) : d244275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31513, d244275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31513, d244275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31519 q = 1) (hb : d241832 q = 1) : d244281 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31519, d244281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31519, d244281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31528 q = 1) (hb : d241832 q = 1) : d244290 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31528, d244290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31528, d244290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31529 q = 1) (hb : d241832 q = 1) : d244291 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31529, d244291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31529, d244291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79121 (p : Pattern) (ha : d31600 p = 1) (hb : d241832 p = 1) : d244314 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31530 q = 1) (hb : d241832 q = 1) : d244292 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31530, d244292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79120 q ha hb
    | true =>
      simp only [d31530, d244292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31531 q = 1) (hb : d241832 q = 1) : d244293 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31531, d244293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31531, d244293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31597 q = 1) (hb : d241832 q = 1) : d244311 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31597, d244311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31597, d244311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31598 q = 1) (hb : d241832 q = 1) : d244312 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31598, d244312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31598, d244312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31599 q = 1) (hb : d241832 q = 1) : d244313 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31599, d244313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31599, d244313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31600 q = 1) (hb : d241832 q = 1) : d244314 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31600, d244314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31600, d244314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79122 (p : Pattern) (ha : d31606 p = 1) (hb : d241832 p = 1) : d244320 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31601 q = 1) (hb : d241832 q = 1) : d244315 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31601, d244315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79121 q ha hb
    | true =>
      simp only [d31601, d244315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31602 q = 1) (hb : d241832 q = 1) : d244316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31602, d244316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31602, d244316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31603 q = 1) (hb : d241832 q = 1) : d244317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31603, d244317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31603, d244317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31604 q = 1) (hb : d241832 q = 1) : d244318 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31604, d244318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31604, d244318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31605 q = 1) (hb : d241832 q = 1) : d244319 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31605, d244319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31605, d244319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31606 q = 1) (hb : d241832 q = 1) : d244320 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31606, d244320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31606, d244320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79123 (p : Pattern) (ha : d31286 p = 1) (hb : d241832 p = 1) : d244165 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31252 q = 1) (hb : d241832 q = 1) : d244131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79107 q ha hb
    | true =>
      simp only [d31252, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31253 q = 1) (hb : d241832 q = 1) : d244132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31256 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79108 q ha hb
    | true =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31257 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31258 q = 1) (hb : d241832 q = 1) : d244137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31258, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31258, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31259 q = 1) (hb : d241832 q = 1) : d244138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31259, d244138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31259, d244138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31285 q = 1) (hb : d241832 q = 1) : d244164 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31285, d244164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31285, d244164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31286 q = 1) (hb : d241832 q = 1) : d244165 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31286, d244165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31286, d244165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79124 (p : Pattern) (ha : d31288 p = 1) (hb : d241832 p = 1) : d244167 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31256 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79108 q ha hb
    | true =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31257 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31262 q = 1) (hb : d241832 q = 1) : d244141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31262, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31262, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31263 q = 1) (hb : d241832 q = 1) : d244142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31263, d244142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31263, d244142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31287 q = 1) (hb : d241832 q = 1) : d244166 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31287, d244166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31287, d244166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31288 q = 1) (hb : d241832 q = 1) : d244167 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31288, d244167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31288, d244167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79125 (p : Pattern) (ha : d31295 p = 1) (hb : d241832 p = 1) : d244174 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31252 q = 1) (hb : d241832 q = 1) : d244131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79107 q ha hb
    | true =>
      simp only [d31252, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31253 q = 1) (hb : d241832 q = 1) : d244132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31256 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79108 q ha hb
    | true =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31257 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31258 q = 1) (hb : d241832 q = 1) : d244137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31258, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31258, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31293 q = 1) (hb : d241832 q = 1) : d244172 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31293, d244172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31293, d244172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31294 q = 1) (hb : d241832 q = 1) : d244173 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31294, d244173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31294, d244173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31295 q = 1) (hb : d241832 q = 1) : d244174 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31295, d244174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31295, d244174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79126 (p : Pattern) (ha : d31298 p = 1) (hb : d241832 p = 1) : d244177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31256 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79108 q ha hb
    | true =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31257 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31262 q = 1) (hb : d241832 q = 1) : d244141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31262, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31262, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31296 q = 1) (hb : d241832 q = 1) : d244175 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31296, d244175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31296, d244175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31297 q = 1) (hb : d241832 q = 1) : d244176 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31297, d244176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31297, d244176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31298 q = 1) (hb : d241832 q = 1) : d244177 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31298, d244177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31298, d244177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79127 (p : Pattern) (ha : d31312 p = 1) (hb : d241832 p = 1) : d31755 p = 1 := by
  have h0 (q : Pattern) (ha : d31305 q = 1) (hb : d241831 q = 1) : d31305 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d31307 q = 1) (hb : d241832 q = 1) : d31753 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31307, d241832, d31753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31307, d241832, d31753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d31308 q = 1) (hb : d241832 q = 1) : d31754 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31308, d31754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31308, d31754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30969 q = 1) (hb : d241831 q = 1) : d30969 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d31309 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d31310 q = 1) (hb : d241832 q = 1) : d31323 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31310, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31310, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d31311 q = 1) (hb : d241832 q = 1) : d31324 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31311, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31311, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d31312 q = 1) (hb : d241832 q = 1) : d31755 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31312, d31755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31312, d31755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro79128 (p : Pattern) (ha : d31317 p = 1) (hb : d241832 p = 1) : d31325 p = 1 := by
  have h0 (q : Pattern) (ha : d30969 q = 1) (hb : d241831 q = 1) : d30969 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d30973 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d30974 q = 1) (hb : d241832 q = 1) : d31323 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d30974, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d30974, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d30975 q = 1) (hb : d241832 q = 1) : d31324 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d30975, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30975, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30988 q = 1) (hb : d241832 q = 1) : d30988 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d31317 q = 1) (hb : d241832 q = 1) : d31325 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31317, d31325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31317, d31325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79129 (p : Pattern) (ha : d31331 p = 1) (hb : d241832 p = 1) : d244182 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31313 q = 1) (hb : d241832 q = 1) : d31756 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31313, d31756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79127 q ha hb
    | true =>
      simp only [d31313, d31756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31314 q = 1) (hb : d241832 q = 1) : d31757 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31314, d31757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31314, d31757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31315 q = 1) (hb : d241832 q = 1) : d31758 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31315, d31758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31315, d31758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31316 q = 1) (hb : d241832 q = 1) : d31759 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31316, d31759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31316, d31759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31318 q = 1) (hb : d241832 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31318, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79128 q ha hb
    | true =>
      simp only [d31318, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31319 q = 1) (hb : d241832 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31319, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31319, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31320 q = 1) (hb : d241832 q = 1) : d31328 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31320, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31320, d31328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31321 q = 1) (hb : d241832 q = 1) : d31329 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31321, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31321, d31329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31322 q = 1) (hb : d241832 q = 1) : d244181 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31322, d244181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31322, d244181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31330 q = 1) (hb : d241832 q = 1) : d31330 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d31331 q = 1) (hb : d241832 q = 1) : d244182 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31331, d244182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31331, d244182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79130 (p : Pattern) (ha : d31335 p = 1) (hb : d241832 p = 1) : d244119 p = 1 := by
  have h0 (q : Pattern) (ha : d30993 q = 1) (hb : d241832 q = 1) : d30993 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d31232 q = 1) (hb : d241832 q = 1) : d244112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79103 q ha hb
    | true =>
      simp only [d31232, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31233 q = 1) (hb : d241832 q = 1) : d244113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31233, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d31234 q = 1) (hb : d241832 q = 1) : d244114 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31234, d244114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31234, d244114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31235 q = 1) (hb : d241832 q = 1) : d244115 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31235, d244115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31235, d244115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d31236 q = 1) (hb : d241832 q = 1) : d244116 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31236, d244116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31236, d244116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31239 q = 1) (hb : d241832 q = 1) : d244118 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31239, d244118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31239, d244118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d31335 q = 1) (hb : d241832 q = 1) : d244119 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31335, d244119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31335, d244119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79131 (p : Pattern) (ha : d31341 p = 1) (hb : d241832 p = 1) : d244188 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31332 q = 1) (hb : d241832 q = 1) : d244183 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31332, d244183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79129 q ha hb
    | true =>
      simp only [d31332, d244183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79104 q ha hb
  have h2 (q : Pattern) (ha : d31333 q = 1) (hb : d241832 q = 1) : d244184 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31333, d244184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31333, d244184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31334 q = 1) (hb : d241832 q = 1) : d244185 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31334, d244185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31334, d244185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31336 q = 1) (hb : d241832 q = 1) : d244120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31336, d244120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79104 q ha hb
    | true =>
      simp only [d31336, d244120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79130 q ha hb
  have h5 (q : Pattern) (ha : d31337 q = 1) (hb : d241832 q = 1) : d244121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31337, d244121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31337, d244121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31338 q = 1) (hb : d241832 q = 1) : d244122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31338, d244122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31338, d244122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31339 q = 1) (hb : d241832 q = 1) : d244186 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31339, d244186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31339, d244186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31241 q = 1) (hb : d241832 q = 1) : d244120 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31241, d244120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79104 q ha hb
    | true =>
      simp only [d31241, d244120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79105 q ha hb
  have h9 (q : Pattern) (ha : d31242 q = 1) (hb : d241832 q = 1) : d244121 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31242, d244121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31242, d244121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31243 q = 1) (hb : d241832 q = 1) : d244122 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31243, d244122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31243, d244122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31245 q = 1) (hb : d241832 q = 1) : d244124 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31245, d244124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79105 q ha hb
    | true =>
      simp only [d31245, d244124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79106 q ha hb
  have h12 (q : Pattern) (ha : d31246 q = 1) (hb : d241832 q = 1) : d244125 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31246, d244125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31246, d244125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31247 q = 1) (hb : d241832 q = 1) : d244126 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31247, d244126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31247, d244126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31248 q = 1) (hb : d241832 q = 1) : d244127 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31248, d244127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31248, d244127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d31340 q = 1) (hb : d241832 q = 1) : d244187 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31340, d244187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31340, d244187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d31341 q = 1) (hb : d241832 q = 1) : d244188 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31341, d244188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31341, d244188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro79132 (p : Pattern) (ha : d31347 p = 1) (hb : d241832 p = 1) : d244194 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31342 q = 1) (hb : d241832 q = 1) : d244189 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31342, d244189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79131 q ha hb
    | true =>
      simp only [d31342, d244189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31343 q = 1) (hb : d241832 q = 1) : d244190 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31343, d244190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31343, d244190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31252 q = 1) (hb : d241832 q = 1) : d244131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79107 q ha hb
    | true =>
      simp only [d31252, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31253 q = 1) (hb : d241832 q = 1) : d244132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31344 q = 1) (hb : d241832 q = 1) : d244191 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31344, d244191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31344, d244191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31345 q = 1) (hb : d241832 q = 1) : d244192 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31345, d244192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31345, d244192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31346 q = 1) (hb : d241832 q = 1) : d244193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31346, d244193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31346, d244193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31347 q = 1) (hb : d241832 q = 1) : d244194 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31347, d244194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31347, d244194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79133 (p : Pattern) (ha : d31417 p = 1) (hb : d241832 p = 1) : d244200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31252 q = 1) (hb : d241832 q = 1) : d244131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79107 q ha hb
    | true =>
      simp only [d31252, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31253 q = 1) (hb : d241832 q = 1) : d244132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31414 q = 1) (hb : d241832 q = 1) : d244197 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31414, d244197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31414, d244197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31415 q = 1) (hb : d241832 q = 1) : d244198 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31415, d244198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31415, d244198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31416 q = 1) (hb : d241832 q = 1) : d244199 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31416, d244199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31416, d244199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31417 q = 1) (hb : d241832 q = 1) : d244200 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31417, d244200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31417, d244200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79134 (p : Pattern) (ha : d241832 p = 1) (hb : d245471 p = 1) : d244206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31289 q = 1) (hb : d241832 q = 1) : d244168 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31289, d244168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79123 q ha hb
    | true =>
      simp only [d31289, d244168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79124 q ha hb
  have h2 (q : Pattern) (ha : d31290 q = 1) (hb : d241832 q = 1) : d244169 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31290, d244169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31290, d244169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31291 q = 1) (hb : d241832 q = 1) : d244170 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31291, d244170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31291, d244170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31292 q = 1) (hb : d241832 q = 1) : d244171 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31292, d244171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31292, d244171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31299 q = 1) (hb : d241832 q = 1) : d244178 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31299, d244178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79125 q ha hb
    | true =>
      simp only [d31299, d244178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79126 q ha hb
  have h6 (q : Pattern) (ha : d31300 q = 1) (hb : d241832 q = 1) : d244179 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31300, d244179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31300, d244179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31301 q = 1) (hb : d241832 q = 1) : d244180 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31301, d244180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31301, d244180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31348 q = 1) (hb : d241832 q = 1) : d244195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31348, d244195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79132 q ha hb
    | true =>
      simp only [d31348, d244195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79109 q ha hb
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d245467 q = 1) : d244196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245467, d244196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d245467, d244196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d31418 q = 1) (hb : d241832 q = 1) : d244201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31418, d244201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79133 q ha hb
    | true =>
      simp only [d31418, d244201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31419 q = 1) (hb : d241832 q = 1) : d244202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31419, d244202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31419, d244202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d241832 q = 1) (hb : d245468 q = 1) : d244203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245468, d244203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245468, d244203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d241832 q = 1) (hb : d245469 q = 1) : d244204 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245469, d244204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d245469, d244204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d245470 q = 1) : d244205 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245470, d244205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d245470, d244205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d241832 q = 1) (hb : d245471 q = 1) : d244206 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245471, d244206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245471, d244206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79135 (p : Pattern) (ha : d31424 p = 1) (hb : d241832 p = 1) : d244207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31252 q = 1) (hb : d241832 q = 1) : d244131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79107 q ha hb
    | true =>
      simp only [d31252, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31253 q = 1) (hb : d241832 q = 1) : d244132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31256 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79108 q ha hb
    | true =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31257 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31258 q = 1) (hb : d241832 q = 1) : d244137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31258, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31258, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31259 q = 1) (hb : d241832 q = 1) : d244138 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31259, d244138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31259, d244138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31285 q = 1) (hb : d241832 q = 1) : d244164 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31285, d244164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31285, d244164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31424 q = 1) (hb : d241832 q = 1) : d244207 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31424, d244207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31424, d244207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79136 (p : Pattern) (ha : d31425 p = 1) (hb : d241832 p = 1) : d244208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31256 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79108 q ha hb
    | true =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31257 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31262 q = 1) (hb : d241832 q = 1) : d244141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31262, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31262, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31263 q = 1) (hb : d241832 q = 1) : d244142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31263, d244142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31263, d244142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31287 q = 1) (hb : d241832 q = 1) : d244166 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31287, d244166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31287, d244166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31425 q = 1) (hb : d241832 q = 1) : d244208 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31425, d244208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31425, d244208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79137 (p : Pattern) (ha : d31430 p = 1) (hb : d241832 p = 1) : d244213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31252 q = 1) (hb : d241832 q = 1) : d244131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79107 q ha hb
    | true =>
      simp only [d31252, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31253 q = 1) (hb : d241832 q = 1) : d244132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31256 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79108 q ha hb
    | true =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31257 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31258 q = 1) (hb : d241832 q = 1) : d244137 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31258, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31258, d244137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31293 q = 1) (hb : d241832 q = 1) : d244172 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31293, d244172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31293, d244172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31294 q = 1) (hb : d241832 q = 1) : d244173 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31294, d244173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31294, d244173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31430 q = 1) (hb : d241832 q = 1) : d244213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31430, d244213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31430, d244213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79138 (p : Pattern) (ha : d31431 p = 1) (hb : d241832 p = 1) : d244214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31256 q = 1) (hb : d241832 q = 1) : d244135 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79108 q ha hb
    | true =>
      simp only [d31256, d244135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31257 q = 1) (hb : d241832 q = 1) : d244136 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31257, d244136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31262 q = 1) (hb : d241832 q = 1) : d244141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31262, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31262, d244141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31296 q = 1) (hb : d241832 q = 1) : d244175 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31296, d244175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31296, d244175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31297 q = 1) (hb : d241832 q = 1) : d244176 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31297, d244176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31297, d244176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31431 q = 1) (hb : d241832 q = 1) : d244214 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31431, d244214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31431, d244214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79139 (p : Pattern) (ha : d31435 p = 1) (hb : d241832 p = 1) : d244218 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31342 q = 1) (hb : d241832 q = 1) : d244189 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31342, d244189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79131 q ha hb
    | true =>
      simp only [d31342, d244189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31343 q = 1) (hb : d241832 q = 1) : d244190 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31343, d244190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31343, d244190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31252 q = 1) (hb : d241832 q = 1) : d244131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79107 q ha hb
    | true =>
      simp only [d31252, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31253 q = 1) (hb : d241832 q = 1) : d244132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31344 q = 1) (hb : d241832 q = 1) : d244191 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31344, d244191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31344, d244191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31345 q = 1) (hb : d241832 q = 1) : d244192 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31345, d244192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31345, d244192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31346 q = 1) (hb : d241832 q = 1) : d244193 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31346, d244193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31346, d244193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31435 q = 1) (hb : d241832 q = 1) : d244218 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31435, d244218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31435, d244218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79140 (p : Pattern) (ha : d31441 p = 1) (hb : d241832 p = 1) : d244221 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31252 q = 1) (hb : d241832 q = 1) : d244131 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31252, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79107 q ha hb
    | true =>
      simp only [d31252, d244131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31253 q = 1) (hb : d241832 q = 1) : d244132 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31253, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31253, d244132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31414 q = 1) (hb : d241832 q = 1) : d244197 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31414, d244197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31414, d244197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31415 q = 1) (hb : d241832 q = 1) : d244198 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31415, d244198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31415, d244198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31416 q = 1) (hb : d241832 q = 1) : d244199 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31416, d244199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31416, d244199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31441 q = 1) (hb : d241832 q = 1) : d244221 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31441, d244221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31441, d244221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79141 (p : Pattern) (ha : d241832 p = 1) (hb : d245476 p = 1) : d244227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31289 q = 1) (hb : d241832 q = 1) : d244168 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31289, d244168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79123 q ha hb
    | true =>
      simp only [d31289, d244168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79124 q ha hb
  have h2 (q : Pattern) (ha : d31290 q = 1) (hb : d241832 q = 1) : d244169 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31290, d244169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31290, d244169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31291 q = 1) (hb : d241832 q = 1) : d244170 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31291, d244170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31291, d244170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31292 q = 1) (hb : d241832 q = 1) : d244171 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31292, d244171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31292, d244171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31299 q = 1) (hb : d241832 q = 1) : d244178 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31299, d244178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79125 q ha hb
    | true =>
      simp only [d31299, d244178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79126 q ha hb
  have h6 (q : Pattern) (ha : d31300 q = 1) (hb : d241832 q = 1) : d244179 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31300, d244179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31300, d244179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31301 q = 1) (hb : d241832 q = 1) : d244180 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31301, d244180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31301, d244180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31348 q = 1) (hb : d241832 q = 1) : d244195 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31348, d244195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79132 q ha hb
    | true =>
      simp only [d31348, d244195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79109 q ha hb
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d245467 q = 1) : d244196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245467, d244196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d245467, d244196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d31418 q = 1) (hb : d241832 q = 1) : d244201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31418, d244201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79133 q ha hb
    | true =>
      simp only [d31418, d244201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31419 q = 1) (hb : d241832 q = 1) : d244202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31419, d244202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31419, d244202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d241832 q = 1) (hb : d245468 q = 1) : d244203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245468, d244203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245468, d244203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d241832 q = 1) (hb : d245469 q = 1) : d244204 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245469, d244204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d245469, d244204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d245470 q = 1) : d244205 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245470, d244205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d245470, d244205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d31426 q = 1) (hb : d241832 q = 1) : d244209 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31426, d244209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79135 q ha hb
    | true =>
      simp only [d31426, d244209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79136 q ha hb
  have h16 (q : Pattern) (ha : d31427 q = 1) (hb : d241832 q = 1) : d244210 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31427, d244210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31427, d244210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31428 q = 1) (hb : d241832 q = 1) : d244211 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31428, d244211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31428, d244211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31429 q = 1) (hb : d241832 q = 1) : d244212 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31429, d244212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31429, d244212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31432 q = 1) (hb : d241832 q = 1) : d244215 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31432, d244215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79137 q ha hb
    | true =>
      simp only [d31432, d244215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79138 q ha hb
  have h20 (q : Pattern) (ha : d31433 q = 1) (hb : d241832 q = 1) : d244216 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31433, d244216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31433, d244216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d31434 q = 1) (hb : d241832 q = 1) : d244217 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31434, d244217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d31434, d244217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d31436 q = 1) (hb : d241832 q = 1) : d244219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31436, d244219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79139 q ha hb
    | true =>
      simp only [d31436, d244219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79112 q ha hb
  have h23 (q : Pattern) (ha : d241832 q = 1) (hb : d245472 q = 1) : d244220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245472, d244220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d245472, d244220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d31442 q = 1) (hb : d241832 q = 1) : d244222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31442, d244222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79140 q ha hb
    | true =>
      simp only [d31442, d244222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d31443 q = 1) (hb : d241832 q = 1) : d244223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31443, d244223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d31443, d244223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d241832 q = 1) (hb : d245473 q = 1) : d244224 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245473, d244224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d245473, d244224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d241832 q = 1) (hb : d245474 q = 1) : d244225 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245474, d244225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d245474, d244225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d241832 q = 1) (hb : d245475 q = 1) : d244226 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245475, d244226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d245475, d244226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d241832 q = 1) (hb : d245476 q = 1) : d244227 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245476, d244227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245476, d244227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro79142 (p : Pattern) (ha : d241832 p = 1) (hb : d245483 p = 1) : d244247 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31436 q = 1) (hb : d241832 q = 1) : d244219 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31436, d244219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79139 q ha hb
    | true =>
      simp only [d31436, d244219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79112 q ha hb
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d245472 q = 1) : d244220 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245472, d244220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245472, d244220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d31442 q = 1) (hb : d241832 q = 1) : d244222 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31442, d244222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79140 q ha hb
    | true =>
      simp only [d31442, d244222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31443 q = 1) (hb : d241832 q = 1) : d244223 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31443, d244223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31443, d244223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d245473 q = 1) : d244224 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245473, d244224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245473, d244224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d245481 q = 1) : d244245 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245481, d244245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245481, d244245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d245482 q = 1) : d244246 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245482, d244246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245482, d244246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d245483 q = 1) : d244247 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245483, d244247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245483, d244247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79143 (p : Pattern) (ha : d31489 p = 1) (hb : d241832 p = 1) : d244256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31475 q = 1) (hb : d241832 q = 1) : d31957 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31475, d31957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31475, d31957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79127 q ha hb
  have h2 (q : Pattern) (ha : d31313 q = 1) (hb : d241832 q = 1) : d31756 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31313, d31756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79127 q ha hb
    | true =>
      simp only [d31313, d31756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31476 q = 1) (hb : d241832 q = 1) : d31958 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31476, d31958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31476, d31958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31314 q = 1) (hb : d241832 q = 1) : d31757 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31314, d31757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31314, d31757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31477 q = 1) (hb : d241832 q = 1) : d31959 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31477, d31959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31477, d31959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31478 q = 1) (hb : d241832 q = 1) : d31960 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31478, d31960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31478, d31960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31479 q = 1) (hb : d241832 q = 1) : d31484 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31479, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31479, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79128 q ha hb
  have h8 (q : Pattern) (ha : d31318 q = 1) (hb : d241832 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31318, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79128 q ha hb
    | true =>
      simp only [d31318, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31480 q = 1) (hb : d241832 q = 1) : d31485 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31480, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31480, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31319 q = 1) (hb : d241832 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31319, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31319, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31481 q = 1) (hb : d241832 q = 1) : d31486 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31481, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31481, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31482 q = 1) (hb : d241832 q = 1) : d31487 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31482, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31482, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31483 q = 1) (hb : d241832 q = 1) : d244255 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31483, d244255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31483, d244255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31488 q = 1) (hb : d241832 q = 1) : d31488 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d31489 q = 1) (hb : d241832 q = 1) : d244256 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31489, d244256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31489, d244256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79144 (p : Pattern) (ha : d31495 p = 1) (hb : d241832 p = 1) : d244262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31118 q = 1) (hb : d241832 q = 1) : d31484 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31118, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31118, d31484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79079 q ha hb
  have h2 (q : Pattern) (ha : d30977 q = 1) (hb : d241832 q = 1) : d31326 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30977, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79079 q ha hb
    | true =>
      simp only [d30977, d31326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31119 q = 1) (hb : d241832 q = 1) : d31485 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31119, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31119, d31485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d30978 q = 1) (hb : d241832 q = 1) : d31327 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30978, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d30978, d31327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31120 q = 1) (hb : d241832 q = 1) : d31486 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31120, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31120, d31486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31121 q = 1) (hb : d241832 q = 1) : d31487 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31121, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31121, d31487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31122 q = 1) (hb : d241832 q = 1) : d31127 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31122, d31127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31122, d31127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79080 q ha hb
  have h8 (q : Pattern) (ha : d30982 q = 1) (hb : d241832 q = 1) : d30990 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d30982, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79080 q ha hb
    | true =>
      simp only [d30982, d30990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31123 q = 1) (hb : d241832 q = 1) : d31128 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31123, d31128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31123, d31128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d30983 q = 1) (hb : d241832 q = 1) : d30991 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d30983, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d30983, d30991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31124 q = 1) (hb : d241832 q = 1) : d31129 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31124, d31129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31124, d31129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31125 q = 1) (hb : d241832 q = 1) : d31130 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31125, d31130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31125, d31130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31126 q = 1) (hb : d241832 q = 1) : d31488 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31126, d31488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31126, d31488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31130 q = 1) (hb : d241832 q = 1) : d31130 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d31490 q = 1) (hb : d241832 q = 1) : d244257 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31490, d244257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31490, d244257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79103 q ha hb
  have h16 (q : Pattern) (ha : d31232 q = 1) (hb : d241832 q = 1) : d244112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79103 q ha hb
    | true =>
      simp only [d31232, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d31491 q = 1) (hb : d241832 q = 1) : d244258 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31491, d244258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31491, d244258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d31233 q = 1) (hb : d241832 q = 1) : d244113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31233, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d31492 q = 1) (hb : d241832 q = 1) : d244259 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31492, d244259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d31492, d244259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d31493 q = 1) (hb : d241832 q = 1) : d244260 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31493, d244260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d31493, d244260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d31494 q = 1) (hb : d241832 q = 1) : d244261 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31494, d244261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31494, d244261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d31495 q = 1) (hb : d241832 q = 1) : d244262 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31495, d244262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31495, d244262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro79145 (p : Pattern) (ha : d31500 p = 1) (hb : d241832 p = 1) : d244267 p = 1 := by
  have h0 (q : Pattern) (ha : d31130 q = 1) (hb : d241832 q = 1) : d31130 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d31490 q = 1) (hb : d241832 q = 1) : d244257 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31490, d244257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31490, d244257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79103 q ha hb
  have h3 (q : Pattern) (ha : d31232 q = 1) (hb : d241832 q = 1) : d244112 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31232, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79103 q ha hb
    | true =>
      simp only [d31232, d244112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d31491 q = 1) (hb : d241832 q = 1) : d244258 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31491, d244258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31491, d244258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31233 q = 1) (hb : d241832 q = 1) : d244113 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31233, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31233, d244113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d31492 q = 1) (hb : d241832 q = 1) : d244259 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31492, d244259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31492, d244259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31493 q = 1) (hb : d241832 q = 1) : d244260 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31493, d244260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31493, d244260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d31494 q = 1) (hb : d241832 q = 1) : d244261 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31494, d244261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31494, d244261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d31499 q = 1) (hb : d241832 q = 1) : d244266 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31499, d244266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31499, d244266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h10 (q : Pattern) (ha : d31500 q = 1) (hb : d241832 q = 1) : d244267 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31500, d244267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31500, d244267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro79146 (p : Pattern) (ha : d31516 p = 1) (hb : d241832 p = 1) : d244278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31496 q = 1) (hb : d241832 q = 1) : d244263 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31496, d244263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79143 q ha hb
    | true =>
      simp only [d31496, d244263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79144 q ha hb
  have h2 (q : Pattern) (ha : d31497 q = 1) (hb : d241832 q = 1) : d244264 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31497, d244264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31497, d244264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31498 q = 1) (hb : d241832 q = 1) : d244265 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31498, d244265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31498, d244265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31501 q = 1) (hb : d241832 q = 1) : d244268 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31501, d244268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79144 q ha hb
    | true =>
      simp only [d31501, d244268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79145 q ha hb
  have h5 (q : Pattern) (ha : d31502 q = 1) (hb : d241832 q = 1) : d244269 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31502, d244269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31502, d244269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31503 q = 1) (hb : d241832 q = 1) : d244270 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31503, d244270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31503, d244270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31504 q = 1) (hb : d241832 q = 1) : d244271 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31504, d244271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31504, d244271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31507 q = 1) (hb : d241832 q = 1) : d244268 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31507, d244268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79144 q ha hb
    | true =>
      simp only [d31507, d244268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79118 q ha hb
  have h9 (q : Pattern) (ha : d31508 q = 1) (hb : d241832 q = 1) : d244269 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31508, d244269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31508, d244269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31509 q = 1) (hb : d241832 q = 1) : d244270 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31509, d244270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31509, d244270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31511 q = 1) (hb : d241832 q = 1) : d244273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31511, d244273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79118 q ha hb
    | true =>
      simp only [d31511, d244273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79119 q ha hb
  have h12 (q : Pattern) (ha : d31512 q = 1) (hb : d241832 q = 1) : d244274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31512, d244274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31512, d244274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31513 q = 1) (hb : d241832 q = 1) : d244275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31513, d244275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31513, d244275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31514 q = 1) (hb : d241832 q = 1) : d244276 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31514, d244276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31514, d244276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d31515 q = 1) (hb : d241832 q = 1) : d244277 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31515, d244277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31515, d244277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d31516 q = 1) (hb : d241832 q = 1) : d244278 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31516, d244278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31516, d244278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro79147 (p : Pattern) (ha : d31521 p = 1) (hb : d241832 p = 1) : d244283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31507 q = 1) (hb : d241832 q = 1) : d244268 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31507, d244268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79144 q ha hb
    | true =>
      simp only [d31507, d244268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79118 q ha hb
  have h2 (q : Pattern) (ha : d31508 q = 1) (hb : d241832 q = 1) : d244269 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31508, d244269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31508, d244269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31509 q = 1) (hb : d241832 q = 1) : d244270 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31509, d244270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31509, d244270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31511 q = 1) (hb : d241832 q = 1) : d244273 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31511, d244273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79118 q ha hb
    | true =>
      simp only [d31511, d244273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79119 q ha hb
  have h5 (q : Pattern) (ha : d31512 q = 1) (hb : d241832 q = 1) : d244274 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31512, d244274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31512, d244274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31513 q = 1) (hb : d241832 q = 1) : d244275 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31513, d244275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31513, d244275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31514 q = 1) (hb : d241832 q = 1) : d244276 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31514, d244276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31514, d244276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31519 q = 1) (hb : d241832 q = 1) : d244281 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31519, d244281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31519, d244281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31520 q = 1) (hb : d241832 q = 1) : d244282 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31520, d244282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31520, d244282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31521 q = 1) (hb : d241832 q = 1) : d244283 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31521, d244283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31521, d244283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro79148 (p : Pattern) (ha : d31527 p = 1) (hb : d241832 p = 1) : d244289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31517 q = 1) (hb : d241832 q = 1) : d244279 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31517, d244279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79146 q ha hb
    | true =>
      simp only [d31517, d244279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31518 q = 1) (hb : d241832 q = 1) : d244280 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31518, d244280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31518, d244280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31522 q = 1) (hb : d241832 q = 1) : d244284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31522, d244284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79147 q ha hb
    | true =>
      simp only [d31522, d244284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31523 q = 1) (hb : d241832 q = 1) : d244285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31523, d244285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31523, d244285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31524 q = 1) (hb : d241832 q = 1) : d244286 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31524, d244286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31524, d244286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31525 q = 1) (hb : d241832 q = 1) : d244287 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31525, d244287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31525, d244287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31526 q = 1) (hb : d241832 q = 1) : d244288 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31526, d244288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31526, d244288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31527 q = 1) (hb : d241832 q = 1) : d244289 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31527, d244289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31527, d244289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79149 (p : Pattern) (ha : d31535 p = 1) (hb : d241832 p = 1) : d244297 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31522 q = 1) (hb : d241832 q = 1) : d244284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31522, d244284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79147 q ha hb
    | true =>
      simp only [d31522, d244284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31523 q = 1) (hb : d241832 q = 1) : d244285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31523, d244285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31523, d244285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31530 q = 1) (hb : d241832 q = 1) : d244292 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31530, d244292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79120 q ha hb
    | true =>
      simp only [d31530, d244292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31531 q = 1) (hb : d241832 q = 1) : d244293 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31531, d244293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31531, d244293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31532 q = 1) (hb : d241832 q = 1) : d244294 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31532, d244294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31532, d244294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31533 q = 1) (hb : d241832 q = 1) : d244295 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31533, d244295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31533, d244295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31534 q = 1) (hb : d241832 q = 1) : d244296 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31534, d244296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31534, d244296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31535 q = 1) (hb : d241832 q = 1) : d244297 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31535, d244297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31535, d244297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79150 (p : Pattern) (ha : d31589 p = 1) (hb : d241832 p = 1) : d244303 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31522 q = 1) (hb : d241832 q = 1) : d244284 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31522, d244284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79147 q ha hb
    | true =>
      simp only [d31522, d244284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31523 q = 1) (hb : d241832 q = 1) : d244285 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31523, d244285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31523, d244285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31586 q = 1) (hb : d241832 q = 1) : d244300 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31586, d244300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31586, d244300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31587 q = 1) (hb : d241832 q = 1) : d244301 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31587, d244301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31587, d244301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31588 q = 1) (hb : d241832 q = 1) : d244302 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31588, d244302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31588, d244302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31589 q = 1) (hb : d241832 q = 1) : d244303 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31589, d244303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31589, d244303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79151 (p : Pattern) (ha : d241832 p = 1) (hb : d245493 p = 1) : d244309 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31536 q = 1) (hb : d241832 q = 1) : d244298 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31536, d244298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79148 q ha hb
    | true =>
      simp only [d31536, d244298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79149 q ha hb
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d245489 q = 1) : d244299 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245489, d244299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245489, d244299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d31590 q = 1) (hb : d241832 q = 1) : d244304 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31590, d244304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79150 q ha hb
    | true =>
      simp only [d31590, d244304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31591 q = 1) (hb : d241832 q = 1) : d244305 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31591, d244305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31591, d244305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d245490 q = 1) : d244306 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245490, d244306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245490, d244306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d245491 q = 1) : d244307 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245491, d244307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245491, d244307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d245492 q = 1) : d244308 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245492, d244308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245492, d244308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d245493 q = 1) : d244309 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245493, d244309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245493, d244309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79152 (p : Pattern) (ha : d241832 p = 1) (hb : d245499 p = 1) : d244326 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31272 q = 1) (hb : d241832 q = 1) : d244151 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31272, d244151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31272, d244151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79111 q ha hb
  have h2 (q : Pattern) (ha : d31273 q = 1) (hb : d241832 q = 1) : d244152 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d31273, d244152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31273, d244152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31282 q = 1) (hb : d241832 q = 1) : d244161 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31282, d244161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79111 q ha hb
    | true =>
      simp only [d31282, d244161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79114 q ha hb
  have h4 (q : Pattern) (ha : d31283 q = 1) (hb : d241832 q = 1) : d244162 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d31283, d244162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31283, d244162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31284 q = 1) (hb : d241832 q = 1) : d244163 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d31284, d244163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31284, d244163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d245477 q = 1) : d244228 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245477, d244228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79134 q ha hb
    | true =>
      simp only [d245477, d244228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79141 q ha hb
  have h7 (q : Pattern) (ha : d31461 q = 1) (hb : d241832 q = 1) : d244241 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31461, d244241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79115 q ha hb
    | true =>
      simp only [d31461, d244241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79116 q ha hb
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d245478 q = 1) : d244242 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245478, d244242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245478, d244242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d245479 q = 1) : d244243 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245479, d244243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245479, d244243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d241832 q = 1) (hb : d245480 q = 1) : d244244 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245480, d244244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d245480, d244244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d241832 q = 1) (hb : d245484 q = 1) : d244248 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245484, d244248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245484, d244248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79142 q ha hb
  have h12 (q : Pattern) (ha : d31470 q = 1) (hb : d241832 q = 1) : d244250 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31470, d244250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31470, d244250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79117 q ha hb
  have h13 (q : Pattern) (ha : d241832 q = 1) (hb : d245485 q = 1) : d244251 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245485, d244251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245485, d244251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d245486 q = 1) : d244252 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245486, d244252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245486, d244252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d241832 q = 1) (hb : d245487 q = 1) : d244253 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245487, d244253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245487, d244253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d241832 q = 1) (hb : d245488 q = 1) : d244254 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245488, d244254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245488, d244254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d241832 q = 1) (hb : d245494 q = 1) : d244310 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245494, d244310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245494, d244310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79151 q ha hb
  have h18 (q : Pattern) (ha : d31607 q = 1) (hb : d241832 q = 1) : d244321 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31607, d244321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31607, d244321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79122 q ha hb
  have h19 (q : Pattern) (ha : d241832 q = 1) (hb : d245495 q = 1) : d244322 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245495, d244322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245495, d244322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d241832 q = 1) (hb : d245496 q = 1) : d244323 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245496, d244323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d245496, d244323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d241832 q = 1) (hb : d245497 q = 1) : d244324 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245497, d244324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d245497, d244324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d241832 q = 1) (hb : d245498 q = 1) : d244325 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245498, d244325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245498, d244325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d241832 q = 1) (hb : d245499 q = 1) : d244326 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245499, d244326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245499, d244326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro79153 (p : Pattern) (ha : d241832 p = 1) (hb : d245505 p = 1) : d244332 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d245500 q = 1) : d244327 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245500, d244327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245500, d244327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79152 q ha hb
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d245501 q = 1) : d244328 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245501, d244328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245501, d244328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d245502 q = 1) : d244329 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245502, d244329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245502, d244329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d245503 q = 1) : d244330 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245503, d244330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245503, d244330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d245504 q = 1) : d244331 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245504, d244331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245504, d244331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d245505 q = 1) : d244332 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245505, d244332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245505, d244332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79154 (p : Pattern) (ha : d31626 p = 1) (hb : d241832 p = 1) : d31755 p = 1 := by
  have h0 (q : Pattern) (ha : d31305 q = 1) (hb : d241831 q = 1) : d31305 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d31307 q = 1) (hb : d241832 q = 1) : d31753 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31307, d241832, d31753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31307, d241832, d31753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d31308 q = 1) (hb : d241832 q = 1) : d31754 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31308, d31754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31308, d31754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d30968 q = 1) (hb : d202304 q = 1) : d30968 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d30744 q = 1) (hb : d202304 q = 1) : d30744 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d9771 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d31621 q = 1) (hb : d241830 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d31622 q = 1) (hb : d241830 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31623 q = 1) (hb : d241831 q = 1) : d30969 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31623, d241831, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31623, d241831, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d31309 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d31624 q = 1) (hb : d241832 q = 1) : d31323 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31624, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31624, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d31625 q = 1) (hb : d241832 q = 1) : d31324 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31625, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31625, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h15 (q : Pattern) (ha : d31626 q = 1) (hb : d241832 q = 1) : d31755 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31626, d31755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31626, d31755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79155 (p : Pattern) (ha : d31636 p = 1) (hb : d241832 p = 1) : d31642 p = 1 := by
  have h0 (q : Pattern) (ha : d30968 q = 1) (hb : d202304 q = 1) : d30968 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30744 q = 1) (hb : d202304 q = 1) : d30744 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9771 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31621 q = 1) (hb : d241830 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d31622 q = 1) (hb : d241830 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31623 q = 1) (hb : d241831 q = 1) : d30969 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31623, d241831, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31623, d241831, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d30973 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d31631 q = 1) (hb : d241832 q = 1) : d31323 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31631, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31631, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d31632 q = 1) (hb : d241832 q = 1) : d31324 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31632, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31632, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31635 q = 1) (hb : d241832 q = 1) : d31635 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d31636 q = 1) (hb : d241832 q = 1) : d31642 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31636, d31642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31636, d31642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro79156 (p : Pattern) (ha : d31649 p = 1) (hb : d241832 p = 1) : d244335 p = 1 := by
  have h0 (q : Pattern) (ha : d31633 q = 1) (hb : d241831 q = 1) : d31633 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25435 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d31647 q = 1) (hb : d241832 q = 1) : d31634 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31647, d241832, d31634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31647, d241832, d31634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d31648 q = 1) (hb : d241832 q = 1) : d31635 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31648, d31635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31648, d31635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1117 q = 1) (hb : d241831 q = 1) : d1117 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1118 q = 1) (hb : d241832 q = 1) : d5537 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1118, d241832, d5537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1118, d241832, d5537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d1119 q = 1) (hb : d241832 q = 1) : d5538 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1119, d5538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1119, d5538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d31649 q = 1) (hb : d241832 q = 1) : d244335 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31649, d244335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31649, d244335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro79157 (p : Pattern) (ha : d31655 p = 1) (hb : d241832 p = 1) : d244341 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31627 q = 1) (hb : d241832 q = 1) : d31756 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31627, d31756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79154 q ha hb
    | true =>
      simp only [d31627, d31756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31628 q = 1) (hb : d241832 q = 1) : d31757 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31628, d31757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31628, d31757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31629 q = 1) (hb : d241832 q = 1) : d31758 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31629, d31758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31629, d31758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31630 q = 1) (hb : d241832 q = 1) : d31759 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31630, d31759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31630, d31759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31637 q = 1) (hb : d241832 q = 1) : d31643 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31637, d31643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79155 q ha hb
    | true =>
      simp only [d31637, d31643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31638 q = 1) (hb : d241832 q = 1) : d31644 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31638, d31644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31638, d31644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31639 q = 1) (hb : d241832 q = 1) : d31645 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31639, d31645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31639, d31645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31640 q = 1) (hb : d241832 q = 1) : d31646 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31640, d31646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31640, d31646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31641 q = 1) (hb : d241832 q = 1) : d31760 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31641, d31760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31641, d31760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31646 q = 1) (hb : d241832 q = 1) : d31646 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d31650 q = 1) (hb : d241832 q = 1) : d244336 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79156 q ha hb
    | true =>
      simp only [d31650, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d31651 q = 1) (hb : d241832 q = 1) : d244337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31651, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31652 q = 1) (hb : d241832 q = 1) : d244338 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31652, d244338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31652, d244338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31653 q = 1) (hb : d241832 q = 1) : d244339 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31653, d244339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31653, d244339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31654 q = 1) (hb : d241832 q = 1) : d244340 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31654, d244340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31654, d244340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d31655 q = 1) (hb : d241832 q = 1) : d244341 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31655, d244341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31655, d244341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro79158 (p : Pattern) (ha : d31661 p = 1) (hb : d241832 p = 1) : d31642 p = 1 := by
  have h0 (q : Pattern) (ha : d30968 q = 1) (hb : d202304 q = 1) : d30968 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30744 q = 1) (hb : d202304 q = 1) : d30744 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9771 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31621 q = 1) (hb : d241830 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d31622 q = 1) (hb : d241830 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31623 q = 1) (hb : d241831 q = 1) : d30969 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31623, d241831, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31623, d241831, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d30973 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d31631 q = 1) (hb : d241832 q = 1) : d31323 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31631, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31631, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d31632 q = 1) (hb : d241832 q = 1) : d31324 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31632, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31632, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31622 q = 1) (hb : d202304 q = 1) : d31622 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d25432 q = 1) (hb : d202304 q = 1) : d25432 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d18 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d31656 q = 1) (hb : d241830 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31656, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31656, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d31657 q = 1) (hb : d241830 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31657, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31657, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d31658 q = 1) (hb : d241831 q = 1) : d31633 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31658, d241831, d31633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31658, d241831, d31633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d30635 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d31659 q = 1) (hb : d241832 q = 1) : d31634 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31659, d241832, d31634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31659, d241832, d31634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d31660 q = 1) (hb : d241832 q = 1) : d31635 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31660, d31635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d31660, d31635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h20 (q : Pattern) (ha : d31661 q = 1) (hb : d241832 q = 1) : d31642 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31661, d31642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31661, d31642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro79159 (p : Pattern) (ha : d31666 p = 1) (hb : d241832 p = 1) : d244335 p = 1 := by
  have h0 (q : Pattern) (ha : d31622 q = 1) (hb : d202304 q = 1) : d31622 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25432 q = 1) (hb : d202304 q = 1) : d25432 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31656 q = 1) (hb : d241830 q = 1) : d25433 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31656, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31656, d241830, d25433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d31657 q = 1) (hb : d241830 q = 1) : d25434 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31657, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31657, d25434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31658 q = 1) (hb : d241831 q = 1) : d31633 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31658, d241831, d31633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31658, d241831, d31633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d30635 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d31659 q = 1) (hb : d241832 q = 1) : d31634 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31659, d241832, d31634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31659, d241832, d31634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d31660 q = 1) (hb : d241832 q = 1) : d31635 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31660, d31635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31660, d31635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1117 q = 1) (hb : d241831 q = 1) : d1117 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d1118 q = 1) (hb : d241832 q = 1) : d5537 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d1118, d241832, d5537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1118, d241832, d5537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d1119 q = 1) (hb : d241832 q = 1) : d5538 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d1119, d5538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1119, d5538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h15 (q : Pattern) (ha : d31666 q = 1) (hb : d241832 q = 1) : d244335 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31666, d244335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31666, d244335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79160 (p : Pattern) (ha : d31673 p = 1) (hb : d241832 p = 1) : d244343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31662 q = 1) (hb : d241832 q = 1) : d31643 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31662, d31643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79158 q ha hb
    | true =>
      simp only [d31662, d31643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31663 q = 1) (hb : d241832 q = 1) : d31644 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31663, d31644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31663, d31644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31664 q = 1) (hb : d241832 q = 1) : d31645 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31664, d31645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31664, d31645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31665 q = 1) (hb : d241832 q = 1) : d31646 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31665, d31646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31665, d31646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31667 q = 1) (hb : d241832 q = 1) : d244336 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79159 q ha hb
    | true =>
      simp only [d31667, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31668 q = 1) (hb : d241832 q = 1) : d244337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31668, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31669 q = 1) (hb : d241832 q = 1) : d244338 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31669, d244338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31669, d244338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31670 q = 1) (hb : d241832 q = 1) : d244339 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31670, d244339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31670, d244339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31671 q = 1) (hb : d241832 q = 1) : d244340 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31671, d244340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31671, d244340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31650 q = 1) (hb : d241832 q = 1) : d244336 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79156 q ha hb
    | true =>
      simp only [d31650, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31651 q = 1) (hb : d241832 q = 1) : d244337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31651, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d31652 q = 1) (hb : d241832 q = 1) : d244338 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31652, d244338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31652, d244338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31653 q = 1) (hb : d241832 q = 1) : d244339 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31653, d244339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31653, d244339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d31672 q = 1) (hb : d241832 q = 1) : d244342 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31672, d244342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31672, d244342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31673 q = 1) (hb : d241832 q = 1) : d244343 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31673, d244343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31673, d244343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79161 (p : Pattern) (ha : d9843 p = 1) (hb : d241832 p = 1) : d1135 p = 1 := by
  have h0 (q : Pattern) (ha : d1132 q = 1) (hb : d241831 q = 1) : d1132 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d21 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d9841 q = 1) (hb : d241832 q = 1) : d1133 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9841, d241832, d1133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d9841, d241832, d1133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d9842 q = 1) (hb : d241832 q = 1) : d1134 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9842, d1134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9842, d1134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9843 q = 1) (hb : d241832 q = 1) : d1135 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d9843, d1135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9843, d1135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro79162 (p : Pattern) (ha : d31678 p = 1) (hb : d241832 p = 1) : d244347 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31667 q = 1) (hb : d241832 q = 1) : d244336 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79159 q ha hb
    | true =>
      simp only [d31667, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31668 q = 1) (hb : d241832 q = 1) : d244337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31668, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31669 q = 1) (hb : d241832 q = 1) : d244338 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31669, d244338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31669, d244338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31670 q = 1) (hb : d241832 q = 1) : d244339 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31670, d244339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31670, d244339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31677 q = 1) (hb : d241832 q = 1) : d244342 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31677, d244342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31677, d244342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d9844 q = 1) (hb : d241832 q = 1) : d1136 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d1136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79161 q ha hb
    | true =>
      simp only [d9844, d1136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d9846 q = 1) (hb : d241832 q = 1) : d1137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d1137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9846, d1137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d14770 q = 1) (hb : d241832 q = 1) : d1138 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d14770, d1138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14770, d1138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d14771 q = 1) (hb : d241832 q = 1) : d1139 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d14771, d1139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d14771, d1139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d14772 q = 1) (hb : d241832 q = 1) : d1140 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d14772, d1140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d14772, d1140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31678 q = 1) (hb : d241832 q = 1) : d244347 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31678, d244347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31678, d244347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79163 (p : Pattern) (ha : d31685 p = 1) (hb : d241832 p = 1) : d244354 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31674 q = 1) (hb : d241832 q = 1) : d244344 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31674, d244344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79157 q ha hb
    | true =>
      simp only [d31674, d244344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79160 q ha hb
  have h2 (q : Pattern) (ha : d31675 q = 1) (hb : d241832 q = 1) : d244345 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31675, d244345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31675, d244345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31676 q = 1) (hb : d241832 q = 1) : d244346 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31676, d244346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31676, d244346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31679 q = 1) (hb : d241832 q = 1) : d244348 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31679, d244348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79160 q ha hb
    | true =>
      simp only [d31679, d244348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79162 q ha hb
  have h5 (q : Pattern) (ha : d31680 q = 1) (hb : d241832 q = 1) : d244349 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31680, d244349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31680, d244349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31681 q = 1) (hb : d241832 q = 1) : d244350 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31681, d244350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31681, d244350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31682 q = 1) (hb : d241832 q = 1) : d244351 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31682, d244351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31682, d244351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31683 q = 1) (hb : d241832 q = 1) : d244352 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31683, d244352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31683, d244352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31684 q = 1) (hb : d241832 q = 1) : d244353 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31684, d244353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31684, d244353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31685 q = 1) (hb : d241832 q = 1) : d244354 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31685, d244354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31685, d244354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro79164 (p : Pattern) (ha : d31689 p = 1) (hb : d241832 p = 1) : d244358 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31679 q = 1) (hb : d241832 q = 1) : d244348 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31679, d244348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79160 q ha hb
    | true =>
      simp only [d31679, d244348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79162 q ha hb
  have h2 (q : Pattern) (ha : d31680 q = 1) (hb : d241832 q = 1) : d244349 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31680, d244349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31680, d244349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31681 q = 1) (hb : d241832 q = 1) : d244350 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31681, d244350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31681, d244350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31683 q = 1) (hb : d241832 q = 1) : d244352 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31683, d244352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31683, d244352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31688 q = 1) (hb : d241832 q = 1) : d244357 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31688, d244357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31688, d244357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31689 q = 1) (hb : d241832 q = 1) : d244358 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31689, d244358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31689, d244358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79165 (p : Pattern) (ha : d31695 p = 1) (hb : d241832 p = 1) : d244364 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d241832 q = 1) : d244355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d244355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79163 q ha hb
    | true =>
      simp only [d31686, d244355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d241832 q = 1) : d244356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d244356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d244356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d241832 q = 1) : d244359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79164 q ha hb
    | true =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d241832 q = 1) : d244360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d241832 q = 1) : d244361 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d244361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d244361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31693 q = 1) (hb : d241832 q = 1) : d244362 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31693, d244362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31693, d244362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31694 q = 1) (hb : d241832 q = 1) : d244363 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31694, d244363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31694, d244363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31695 q = 1) (hb : d241832 q = 1) : d244364 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31695, d244364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31695, d244364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79166 (p : Pattern) (ha : d31699 p = 1) (hb : d241832 p = 1) : d244368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d241832 q = 1) : d244359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79164 q ha hb
    | true =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d241832 q = 1) : d244360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d241832 q = 1) : d244365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d244365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d244365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31697 q = 1) (hb : d241832 q = 1) : d244366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31697, d244366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31697, d244366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31698 q = 1) (hb : d241832 q = 1) : d244367 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31698, d244367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31698, d244367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31699 q = 1) (hb : d241832 q = 1) : d244368 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31699, d244368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31699, d244368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79167 (p : Pattern) (ha : d31705 p = 1) (hb : d241832 p = 1) : d244374 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31700 q = 1) (hb : d241832 q = 1) : d244369 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31700, d244369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79165 q ha hb
    | true =>
      simp only [d31700, d244369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79166 q ha hb
  have h2 (q : Pattern) (ha : d31701 q = 1) (hb : d241832 q = 1) : d244370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31701, d244370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31701, d244370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31702 q = 1) (hb : d241832 q = 1) : d244371 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31702, d244371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31702, d244371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31703 q = 1) (hb : d241832 q = 1) : d244372 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31703, d244372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31703, d244372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31704 q = 1) (hb : d241832 q = 1) : d244373 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31704, d244373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31704, d244373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31705 q = 1) (hb : d241832 q = 1) : d244374 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31705, d244374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31705, d244374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79168 (p : Pattern) (ha : d31708 p = 1) (hb : d241832 p = 1) : d244377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d241832 q = 1) : d244355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d244355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79163 q ha hb
    | true =>
      simp only [d31686, d244355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d241832 q = 1) : d244356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d244356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d244356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d241832 q = 1) : d244359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79164 q ha hb
    | true =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d241832 q = 1) : d244360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d241832 q = 1) : d244361 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d244361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d244361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31693 q = 1) (hb : d241832 q = 1) : d244362 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31693, d244362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31693, d244362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31694 q = 1) (hb : d241832 q = 1) : d244363 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31694, d244363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31694, d244363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31708 q = 1) (hb : d241832 q = 1) : d244377 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31708, d244377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31708, d244377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79169 (p : Pattern) (ha : d31709 p = 1) (hb : d241832 p = 1) : d244378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d241832 q = 1) : d244359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79164 q ha hb
    | true =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d241832 q = 1) : d244360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d241832 q = 1) : d244365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d244365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d244365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31697 q = 1) (hb : d241832 q = 1) : d244366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31697, d244366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31697, d244366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31698 q = 1) (hb : d241832 q = 1) : d244367 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31698, d244367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31698, d244367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31709 q = 1) (hb : d241832 q = 1) : d244378 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31709, d244378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31709, d244378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79170 (p : Pattern) (ha : d31715 p = 1) (hb : d241832 p = 1) : d244384 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31700 q = 1) (hb : d241832 q = 1) : d244369 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31700, d244369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79165 q ha hb
    | true =>
      simp only [d31700, d244369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79166 q ha hb
  have h2 (q : Pattern) (ha : d31701 q = 1) (hb : d241832 q = 1) : d244370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31701, d244370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31701, d244370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31702 q = 1) (hb : d241832 q = 1) : d244371 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31702, d244371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31702, d244371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31703 q = 1) (hb : d241832 q = 1) : d244372 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31703, d244372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31703, d244372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31704 q = 1) (hb : d241832 q = 1) : d244373 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31704, d244373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31704, d244373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31710 q = 1) (hb : d241832 q = 1) : d244379 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31710, d244379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79168 q ha hb
    | true =>
      simp only [d31710, d244379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79169 q ha hb
  have h7 (q : Pattern) (ha : d31711 q = 1) (hb : d241832 q = 1) : d244380 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31711, d244380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31711, d244380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31712 q = 1) (hb : d241832 q = 1) : d244381 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31712, d244381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31712, d244381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31713 q = 1) (hb : d241832 q = 1) : d244382 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31713, d244382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31713, d244382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31714 q = 1) (hb : d241832 q = 1) : d244383 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31714, d244383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31714, d244383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31715 q = 1) (hb : d241832 q = 1) : d244384 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31715, d244384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31715, d244384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79171 (p : Pattern) (ha : d31927 p = 1) (hb : d241832 p = 1) : d244472 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31700 q = 1) (hb : d241832 q = 1) : d244369 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31700, d244369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79165 q ha hb
    | true =>
      simp only [d31700, d244369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79166 q ha hb
  have h2 (q : Pattern) (ha : d31701 q = 1) (hb : d241832 q = 1) : d244370 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31701, d244370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31701, d244370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31702 q = 1) (hb : d241832 q = 1) : d244371 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31702, d244371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31702, d244371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31703 q = 1) (hb : d241832 q = 1) : d244372 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31703, d244372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31703, d244372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31704 q = 1) (hb : d241832 q = 1) : d244373 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31704, d244373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31704, d244373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31922 q = 1) (hb : d241832 q = 1) : d244467 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31922, d244467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79166 q ha hb
    | true =>
      simp only [d31922, d244467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31923 q = 1) (hb : d241832 q = 1) : d244468 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31923, d244468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31923, d244468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31924 q = 1) (hb : d241832 q = 1) : d244469 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31924, d244469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31924, d244469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31925 q = 1) (hb : d241832 q = 1) : d244470 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31925, d244470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31925, d244470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31926 q = 1) (hb : d241832 q = 1) : d244471 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31926, d244471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31926, d244471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31927 q = 1) (hb : d241832 q = 1) : d244472 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31927, d244472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31927, d244472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79172 (p : Pattern) (ha : d31933 p = 1) (hb : d241832 p = 1) : d244478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31922 q = 1) (hb : d241832 q = 1) : d244467 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31922, d244467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79166 q ha hb
    | true =>
      simp only [d31922, d244467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31923 q = 1) (hb : d241832 q = 1) : d244468 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31923, d244468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31923, d244468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31924 q = 1) (hb : d241832 q = 1) : d244469 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31924, d244469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31924, d244469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31925 q = 1) (hb : d241832 q = 1) : d244470 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31925, d244470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31925, d244470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31926 q = 1) (hb : d241832 q = 1) : d244471 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31926, d244471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31926, d244471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31928 q = 1) (hb : d241832 q = 1) : d244473 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31928, d244473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79169 q ha hb
    | true =>
      simp only [d31928, d244473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31929 q = 1) (hb : d241832 q = 1) : d244474 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31929, d244474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31929, d244474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31930 q = 1) (hb : d241832 q = 1) : d244475 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31930, d244475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31930, d244475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31931 q = 1) (hb : d241832 q = 1) : d244476 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31931, d244476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31931, d244476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31932 q = 1) (hb : d241832 q = 1) : d244477 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31932, d244477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31932, d244477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31933 q = 1) (hb : d241832 q = 1) : d244478 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31933, d244478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31933, d244478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79173 (p : Pattern) (ha : d31942 p = 1) (hb : d241832 p = 1) : d244487 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31928 q = 1) (hb : d241832 q = 1) : d244473 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31928, d244473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79169 q ha hb
    | true =>
      simp only [d31928, d244473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31929 q = 1) (hb : d241832 q = 1) : d244474 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31929, d244474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31929, d244474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31930 q = 1) (hb : d241832 q = 1) : d244475 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31930, d244475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31930, d244475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31931 q = 1) (hb : d241832 q = 1) : d244476 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31931, d244476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31931, d244476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31932 q = 1) (hb : d241832 q = 1) : d244477 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d31932, d244477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31932, d244477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31942 q = 1) (hb : d241832 q = 1) : d244487 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d31942, d244487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31942, d244487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79174 (p : Pattern) (ha : d32005 p = 1) (hb : d241832 p = 1) : d244509 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31996 q = 1) (hb : d241832 q = 1) : d31961 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31996, d31961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31996, d31961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79158 q ha hb
  have h2 (q : Pattern) (ha : d31662 q = 1) (hb : d241832 q = 1) : d31643 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31662, d31643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79158 q ha hb
    | true =>
      simp only [d31662, d31643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31997 q = 1) (hb : d241832 q = 1) : d31962 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31997, d31962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31997, d31962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31663 q = 1) (hb : d241832 q = 1) : d31644 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31663, d31644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31663, d31644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31998 q = 1) (hb : d241832 q = 1) : d31963 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31998, d31963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31998, d31963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31999 q = 1) (hb : d241832 q = 1) : d31964 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31999, d31964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31999, d31964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32000 q = 1) (hb : d241832 q = 1) : d244499 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32000, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32000, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79159 q ha hb
  have h8 (q : Pattern) (ha : d31667 q = 1) (hb : d241832 q = 1) : d244336 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79159 q ha hb
    | true =>
      simp only [d31667, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32001 q = 1) (hb : d241832 q = 1) : d244500 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32001, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32001, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31668 q = 1) (hb : d241832 q = 1) : d244337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31668, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32002 q = 1) (hb : d241832 q = 1) : d244501 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32002, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32002, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32003 q = 1) (hb : d241832 q = 1) : d244502 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32003, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32003, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d32004 q = 1) (hb : d241832 q = 1) : d244503 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32004, d244503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32004, d244503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31976 q = 1) (hb : d241832 q = 1) : d244499 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31976, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31976, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79156 q ha hb
  have h15 (q : Pattern) (ha : d31650 q = 1) (hb : d241832 q = 1) : d244336 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79156 q ha hb
    | true =>
      simp only [d31650, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d31977 q = 1) (hb : d241832 q = 1) : d244500 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31977, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31977, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31651 q = 1) (hb : d241832 q = 1) : d244337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31651, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31978 q = 1) (hb : d241832 q = 1) : d244501 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31978, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31978, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31979 q = 1) (hb : d241832 q = 1) : d244502 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31979, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d31979, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d31990 q = 1) (hb : d241832 q = 1) : d244508 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31990, d244508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d31990, d244508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d32005 q = 1) (hb : d241832 q = 1) : d244509 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32005, d244509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32005, d244509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro79175 (p : Pattern) (ha : d32010 p = 1) (hb : d241832 p = 1) : d244514 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32000 q = 1) (hb : d241832 q = 1) : d244499 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32000, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32000, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79159 q ha hb
  have h2 (q : Pattern) (ha : d31667 q = 1) (hb : d241832 q = 1) : d244336 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79159 q ha hb
    | true =>
      simp only [d31667, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32001 q = 1) (hb : d241832 q = 1) : d244500 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32001, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32001, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31668 q = 1) (hb : d241832 q = 1) : d244337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31668, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32002 q = 1) (hb : d241832 q = 1) : d244501 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32002, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32002, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32003 q = 1) (hb : d241832 q = 1) : d244502 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32003, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32003, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32009 q = 1) (hb : d241832 q = 1) : d244508 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32009, d244508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32009, d244508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15019 q = 1) (hb : d241832 q = 1) : d1406 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d1406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, d1406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79161 q ha hb
  have h9 (q : Pattern) (ha : d9844 q = 1) (hb : d241832 q = 1) : d1136 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d1136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79161 q ha hb
    | true =>
      simp only [d9844, d1136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15020 q = 1) (hb : d241832 q = 1) : d1407 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, d1407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15020, d1407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9846 q = 1) (hb : d241832 q = 1) : d1137 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d1137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9846, d1137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15021 q = 1) (hb : d241832 q = 1) : d1408 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15021, d1408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15021, d1408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15022 q = 1) (hb : d241832 q = 1) : d1409 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15022, d1409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15022, d1409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15023 q = 1) (hb : d241832 q = 1) : d1410 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15023, d1410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15023, d1410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d32010 q = 1) (hb : d241832 q = 1) : d244514 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32010, d244514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32010, d244514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79176 (p : Pattern) (ha : d32029 p = 1) (hb : d241832 p = 1) : d244533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32011 q = 1) (hb : d241832 q = 1) : d244515 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32011, d244515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79174 q ha hb
    | true =>
      simp only [d32011, d244515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79175 q ha hb
  have h2 (q : Pattern) (ha : d32012 q = 1) (hb : d241832 q = 1) : d244516 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32012, d244516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32012, d244516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32013 q = 1) (hb : d241832 q = 1) : d244517 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32013, d244517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32013, d244517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32019 q = 1) (hb : d241832 q = 1) : d244523 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32019, d244523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32019, d244523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32028 q = 1) (hb : d241832 q = 1) : d244532 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32028, d244532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32028, d244532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32029 q = 1) (hb : d241832 q = 1) : d244533 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32029, d244533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32029, d244533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79177 (p : Pattern) (ha : d32118 p = 1) (hb : d241832 p = 1) : d244565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32030 q = 1) (hb : d241832 q = 1) : d244534 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32030, d244534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79176 q ha hb
    | true =>
      simp only [d32030, d244534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32031 q = 1) (hb : d241832 q = 1) : d244535 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32031, d244535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32031, d244535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32115 q = 1) (hb : d241832 q = 1) : d244562 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32115, d244562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32115, d244562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32116 q = 1) (hb : d241832 q = 1) : d244563 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32116, d244563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32116, d244563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32117 q = 1) (hb : d241832 q = 1) : d244564 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32117, d244564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32117, d244564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32118 q = 1) (hb : d241832 q = 1) : d244565 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32118, d244565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32118, d244565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79178 (p : Pattern) (ha : d32124 p = 1) (hb : d241832 p = 1) : d244571 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32119 q = 1) (hb : d241832 q = 1) : d244566 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32119, d244566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79177 q ha hb
    | true =>
      simp only [d32119, d244566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32120 q = 1) (hb : d241832 q = 1) : d244567 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32120, d244567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32120, d244567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32121 q = 1) (hb : d241832 q = 1) : d244568 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32121, d244568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32121, d244568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32122 q = 1) (hb : d241832 q = 1) : d244569 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32122, d244569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32122, d244569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32123 q = 1) (hb : d241832 q = 1) : d244570 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32123, d244570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32123, d244570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32124 q = 1) (hb : d241832 q = 1) : d244571 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32124, d244571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32124, d244571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79179 (p : Pattern) (ha : d31720 p = 1) (hb : d241832 p = 1) : d244389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d241832 q = 1) : d244355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d244355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79163 q ha hb
    | true =>
      simp only [d31686, d244355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d241832 q = 1) : d244356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d244356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d244356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d241832 q = 1) : d244359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79164 q ha hb
    | true =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d241832 q = 1) : d244360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d241832 q = 1) : d244361 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d244361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d244361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31693 q = 1) (hb : d241832 q = 1) : d244362 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31693, d244362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31693, d244362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31719 q = 1) (hb : d241832 q = 1) : d244388 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31719, d244388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31719, d244388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31720 q = 1) (hb : d241832 q = 1) : d244389 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31720, d244389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31720, d244389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79180 (p : Pattern) (ha : d31722 p = 1) (hb : d241832 p = 1) : d244391 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d241832 q = 1) : d244359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79164 q ha hb
    | true =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d241832 q = 1) : d244360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d241832 q = 1) : d244365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d244365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d244365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31697 q = 1) (hb : d241832 q = 1) : d244366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31697, d244366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31697, d244366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31721 q = 1) (hb : d241832 q = 1) : d244390 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31721, d244390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31721, d244390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31722 q = 1) (hb : d241832 q = 1) : d244391 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31722, d244391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31722, d244391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79181 (p : Pattern) (ha : d31729 p = 1) (hb : d241832 p = 1) : d244398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d241832 q = 1) : d244355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d244355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79163 q ha hb
    | true =>
      simp only [d31686, d244355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d241832 q = 1) : d244356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d244356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d244356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d241832 q = 1) : d244359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79164 q ha hb
    | true =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d241832 q = 1) : d244360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d241832 q = 1) : d244361 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d244361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d244361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31727 q = 1) (hb : d241832 q = 1) : d244396 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31727, d244396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31727, d244396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31728 q = 1) (hb : d241832 q = 1) : d244397 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31728, d244397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31728, d244397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31729 q = 1) (hb : d241832 q = 1) : d244398 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31729, d244398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31729, d244398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79182 (p : Pattern) (ha : d31732 p = 1) (hb : d241832 p = 1) : d244401 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d241832 q = 1) : d244359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79164 q ha hb
    | true =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d241832 q = 1) : d244360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d241832 q = 1) : d244365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d244365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d244365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31730 q = 1) (hb : d241832 q = 1) : d244399 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31730, d244399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31730, d244399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31731 q = 1) (hb : d241832 q = 1) : d244400 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31731, d244400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31731, d244400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31732 q = 1) (hb : d241832 q = 1) : d244401 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31732, d244401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31732, d244401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79183 (p : Pattern) (ha : d31742 p = 1) (hb : d241832 p = 1) : d244405 p = 1 := by
  have h0 (q : Pattern) (ha : d31738 q = 1) (hb : d241832 q = 1) : d31738 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31305 q = 1) (hb : d241831 q = 1) : d31305 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d31739 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31740 q = 1) (hb : d241832 q = 1) : d31753 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31740, d241832, d31753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31740, d241832, d31753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d31741 q = 1) (hb : d241832 q = 1) : d31754 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31741, d31754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31741, d31754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31742 q = 1) (hb : d241832 q = 1) : d244405 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31742, d244405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31742, d244405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79184 (p : Pattern) (ha : d31747 p = 1) (hb : d241832 p = 1) : d31755 p = 1 := by
  have h0 (q : Pattern) (ha : d31305 q = 1) (hb : d241831 q = 1) : d31305 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d31306 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d31307 q = 1) (hb : d241832 q = 1) : d31753 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31307, d241832, d31753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31307, d241832, d31753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d31308 q = 1) (hb : d241832 q = 1) : d31754 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31308, d31754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31308, d31754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31324 q = 1) (hb : d241832 q = 1) : d31324 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d31747 q = 1) (hb : d241832 q = 1) : d31755 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31747, d31755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31747, d31755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79185 (p : Pattern) (ha : d31761 p = 1) (hb : d241832 p = 1) : d244411 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31743 q = 1) (hb : d241832 q = 1) : d244406 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31743, d244406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79183 q ha hb
    | true =>
      simp only [d31743, d244406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31744 q = 1) (hb : d241832 q = 1) : d244407 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31744, d244407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31744, d244407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31745 q = 1) (hb : d241832 q = 1) : d244408 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31745, d244408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31745, d244408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31746 q = 1) (hb : d241832 q = 1) : d244409 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31746, d244409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31746, d244409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31748 q = 1) (hb : d241832 q = 1) : d31756 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31748, d31756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79184 q ha hb
    | true =>
      simp only [d31748, d31756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31749 q = 1) (hb : d241832 q = 1) : d31757 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31749, d31757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31749, d31757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31750 q = 1) (hb : d241832 q = 1) : d31758 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31750, d31758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31750, d31758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31751 q = 1) (hb : d241832 q = 1) : d31759 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31751, d31759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31751, d31759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31752 q = 1) (hb : d241832 q = 1) : d244410 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31752, d244410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31752, d244410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31760 q = 1) (hb : d241832 q = 1) : d31760 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d31761 q = 1) (hb : d241832 q = 1) : d244411 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31761, d244411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31761, d244411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79186 (p : Pattern) (ha : d31767 p = 1) (hb : d241832 p = 1) : d31642 p = 1 := by
  have h0 (q : Pattern) (ha : d30968 q = 1) (hb : d202304 q = 1) : d30968 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d30744 q = 1) (hb : d202304 q = 1) : d30744 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d9771 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d31621 q = 1) (hb : d241830 q = 1) : d30745 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31621, d241830, d30745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d31622 q = 1) (hb : d241830 q = 1) : d30746 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31622, d30746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31623 q = 1) (hb : d241831 q = 1) : d30969 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d31623, d241831, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31623, d241831, d30969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d31765 q = 1) (hb : d241832 q = 1) : d31323 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d31765, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31765, d241832, d31323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d31766 q = 1) (hb : d241832 q = 1) : d31324 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d31766, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31766, d31324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31635 q = 1) (hb : d241832 q = 1) : d31635 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d31767 q = 1) (hb : d241832 q = 1) : d31642 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d31767, d31642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31767, d31642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro79187 (p : Pattern) (ha : d31773 p = 1) (hb : d241832 p = 1) : d244343 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31768 q = 1) (hb : d241832 q = 1) : d31643 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31768, d31643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79186 q ha hb
    | true =>
      simp only [d31768, d31643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31769 q = 1) (hb : d241832 q = 1) : d31644 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31769, d31644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31769, d31644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31770 q = 1) (hb : d241832 q = 1) : d31645 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31770, d31645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31770, d31645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31771 q = 1) (hb : d241832 q = 1) : d31646 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31771, d31646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31771, d31646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31650 q = 1) (hb : d241832 q = 1) : d244336 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79156 q ha hb
    | true =>
      simp only [d31650, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31651 q = 1) (hb : d241832 q = 1) : d244337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31651, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31652 q = 1) (hb : d241832 q = 1) : d244338 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31652, d244338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31652, d244338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31653 q = 1) (hb : d241832 q = 1) : d244339 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31653, d244339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31653, d244339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31772 q = 1) (hb : d241832 q = 1) : d244340 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31772, d244340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31772, d244340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31672 q = 1) (hb : d241832 q = 1) : d244342 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31672, d244342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31672, d244342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31773 q = 1) (hb : d241832 q = 1) : d244343 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31773, d244343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31773, d244343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79188 (p : Pattern) (ha : d31779 p = 1) (hb : d241832 p = 1) : d244417 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31762 q = 1) (hb : d241832 q = 1) : d244412 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31762, d244412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79185 q ha hb
    | true =>
      simp only [d31762, d244412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79157 q ha hb
  have h2 (q : Pattern) (ha : d31763 q = 1) (hb : d241832 q = 1) : d244413 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31763, d244413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31763, d244413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31764 q = 1) (hb : d241832 q = 1) : d244414 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31764, d244414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31764, d244414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31774 q = 1) (hb : d241832 q = 1) : d244344 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31774, d244344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79157 q ha hb
    | true =>
      simp only [d31774, d244344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79187 q ha hb
  have h5 (q : Pattern) (ha : d31775 q = 1) (hb : d241832 q = 1) : d244345 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31775, d244345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31775, d244345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31776 q = 1) (hb : d241832 q = 1) : d244346 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31776, d244346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31776, d244346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31777 q = 1) (hb : d241832 q = 1) : d244415 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31777, d244415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31777, d244415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31674 q = 1) (hb : d241832 q = 1) : d244344 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31674, d244344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79157 q ha hb
    | true =>
      simp only [d31674, d244344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79160 q ha hb
  have h9 (q : Pattern) (ha : d31675 q = 1) (hb : d241832 q = 1) : d244345 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31675, d244345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31675, d244345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31676 q = 1) (hb : d241832 q = 1) : d244346 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31676, d244346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31676, d244346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31679 q = 1) (hb : d241832 q = 1) : d244348 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31679, d244348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79160 q ha hb
    | true =>
      simp only [d31679, d244348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79162 q ha hb
  have h12 (q : Pattern) (ha : d31680 q = 1) (hb : d241832 q = 1) : d244349 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31680, d244349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31680, d244349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31681 q = 1) (hb : d241832 q = 1) : d244350 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31681, d244350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31681, d244350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31682 q = 1) (hb : d241832 q = 1) : d244351 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31682, d244351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31682, d244351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d31778 q = 1) (hb : d241832 q = 1) : d244416 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31778, d244416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31778, d244416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d31779 q = 1) (hb : d241832 q = 1) : d244417 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31779, d244417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31779, d244417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro79189 (p : Pattern) (ha : d31785 p = 1) (hb : d241832 p = 1) : d244423 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31780 q = 1) (hb : d241832 q = 1) : d244418 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31780, d244418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79188 q ha hb
    | true =>
      simp only [d31780, d244418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31781 q = 1) (hb : d241832 q = 1) : d244419 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31781, d244419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31781, d244419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31686 q = 1) (hb : d241832 q = 1) : d244355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d244355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79163 q ha hb
    | true =>
      simp only [d31686, d244355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31687 q = 1) (hb : d241832 q = 1) : d244356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d244356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d244356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31782 q = 1) (hb : d241832 q = 1) : d244420 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31782, d244420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31782, d244420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31783 q = 1) (hb : d241832 q = 1) : d244421 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31783, d244421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31783, d244421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31784 q = 1) (hb : d241832 q = 1) : d244422 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31784, d244422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31784, d244422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31785 q = 1) (hb : d241832 q = 1) : d244423 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31785, d244423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31785, d244423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79190 (p : Pattern) (ha : d31878 p = 1) (hb : d241832 p = 1) : d244426 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31667 q = 1) (hb : d241832 q = 1) : d244336 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79159 q ha hb
    | true =>
      simp only [d31667, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31668 q = 1) (hb : d241832 q = 1) : d244337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31668, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31669 q = 1) (hb : d241832 q = 1) : d244338 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31669, d244338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31669, d244338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31670 q = 1) (hb : d241832 q = 1) : d244339 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31670, d244339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31670, d244339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31677 q = 1) (hb : d241832 q = 1) : d244342 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31677, d244342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31677, d244342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31878 q = 1) (hb : d241832 q = 1) : d244426 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31878, d244426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31878, d244426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79191 (p : Pattern) (ha : d31884 p = 1) (hb : d241832 p = 1) : d244432 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31674 q = 1) (hb : d241832 q = 1) : d244344 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31674, d244344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79157 q ha hb
    | true =>
      simp only [d31674, d244344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79160 q ha hb
  have h2 (q : Pattern) (ha : d31675 q = 1) (hb : d241832 q = 1) : d244345 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31675, d244345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31675, d244345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31676 q = 1) (hb : d241832 q = 1) : d244346 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31676, d244346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31676, d244346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31679 q = 1) (hb : d241832 q = 1) : d244348 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31679, d244348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79160 q ha hb
    | true =>
      simp only [d31679, d244348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79162 q ha hb
  have h5 (q : Pattern) (ha : d31680 q = 1) (hb : d241832 q = 1) : d244349 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31680, d244349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31680, d244349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31681 q = 1) (hb : d241832 q = 1) : d244350 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31681, d244350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31681, d244350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31682 q = 1) (hb : d241832 q = 1) : d244351 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31682, d244351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31682, d244351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31879 q = 1) (hb : d241832 q = 1) : d244427 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31879, d244427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79160 q ha hb
    | true =>
      simp only [d31879, d244427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79190 q ha hb
  have h9 (q : Pattern) (ha : d31880 q = 1) (hb : d241832 q = 1) : d244428 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31880, d244428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31880, d244428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31881 q = 1) (hb : d241832 q = 1) : d244429 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31881, d244429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31881, d244429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d31882 q = 1) (hb : d241832 q = 1) : d244430 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31882, d244430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31882, d244430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d31883 q = 1) (hb : d241832 q = 1) : d244431 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d31883, d244431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31883, d244431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d31884 q = 1) (hb : d241832 q = 1) : d244432 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d31884, d244432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31884, d244432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro79192 (p : Pattern) (ha : d31890 p = 1) (hb : d241832 p = 1) : d244438 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31885 q = 1) (hb : d241832 q = 1) : d244433 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31885, d244433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79191 q ha hb
    | true =>
      simp only [d31885, d244433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31886 q = 1) (hb : d241832 q = 1) : d244434 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31886, d244434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31886, d244434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31887 q = 1) (hb : d241832 q = 1) : d244435 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31887, d244435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31887, d244435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31888 q = 1) (hb : d241832 q = 1) : d244436 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31888, d244436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31888, d244436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31889 q = 1) (hb : d241832 q = 1) : d244437 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31889, d244437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31889, d244437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31890 q = 1) (hb : d241832 q = 1) : d244438 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31890, d244438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31890, d244438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79193 (p : Pattern) (ha : d241832 p = 1) (hb : d245512 p = 1) : d244444 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31723 q = 1) (hb : d241832 q = 1) : d244392 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31723, d244392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79179 q ha hb
    | true =>
      simp only [d31723, d244392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79180 q ha hb
  have h2 (q : Pattern) (ha : d31724 q = 1) (hb : d241832 q = 1) : d244393 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31724, d244393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31724, d244393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31725 q = 1) (hb : d241832 q = 1) : d244394 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31725, d244394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31725, d244394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31726 q = 1) (hb : d241832 q = 1) : d244395 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31726, d244395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31726, d244395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31733 q = 1) (hb : d241832 q = 1) : d244402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31733, d244402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79181 q ha hb
    | true =>
      simp only [d31733, d244402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79182 q ha hb
  have h6 (q : Pattern) (ha : d31734 q = 1) (hb : d241832 q = 1) : d244403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31734, d244403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31734, d244403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31735 q = 1) (hb : d241832 q = 1) : d244404 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31735, d244404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31735, d244404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31786 q = 1) (hb : d241832 q = 1) : d244424 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31786, d244424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79189 q ha hb
    | true =>
      simp only [d31786, d244424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79165 q ha hb
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d245508 q = 1) : d244425 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245508, d244425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d245508, d244425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d31891 q = 1) (hb : d241832 q = 1) : d244439 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31891, d244439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79192 q ha hb
    | true =>
      simp only [d31891, d244439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31892 q = 1) (hb : d241832 q = 1) : d244440 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31892, d244440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31892, d244440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d241832 q = 1) (hb : d245509 q = 1) : d244441 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245509, d244441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245509, d244441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d241832 q = 1) (hb : d245510 q = 1) : d244442 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245510, d244442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d245510, d244442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d245511 q = 1) : d244443 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245511, d244443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d245511, d244443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d241832 q = 1) (hb : d245512 q = 1) : d244444 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245512, d244444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245512, d244444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79194 (p : Pattern) (ha : d31897 p = 1) (hb : d241832 p = 1) : d244445 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d241832 q = 1) : d244355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d244355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79163 q ha hb
    | true =>
      simp only [d31686, d244355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d241832 q = 1) : d244356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d244356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d244356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d241832 q = 1) : d244359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79164 q ha hb
    | true =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d241832 q = 1) : d244360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d241832 q = 1) : d244361 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d244361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d244361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31693 q = 1) (hb : d241832 q = 1) : d244362 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31693, d244362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31693, d244362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31719 q = 1) (hb : d241832 q = 1) : d244388 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31719, d244388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31719, d244388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31897 q = 1) (hb : d241832 q = 1) : d244445 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31897, d244445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31897, d244445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79195 (p : Pattern) (ha : d31898 p = 1) (hb : d241832 p = 1) : d244446 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d241832 q = 1) : d244359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79164 q ha hb
    | true =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d241832 q = 1) : d244360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d241832 q = 1) : d244365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d244365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d244365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31697 q = 1) (hb : d241832 q = 1) : d244366 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31697, d244366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31697, d244366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31721 q = 1) (hb : d241832 q = 1) : d244390 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31721, d244390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31721, d244390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31898 q = 1) (hb : d241832 q = 1) : d244446 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31898, d244446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31898, d244446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79196 (p : Pattern) (ha : d31903 p = 1) (hb : d241832 p = 1) : d244451 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31686 q = 1) (hb : d241832 q = 1) : d244355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d244355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79163 q ha hb
    | true =>
      simp only [d31686, d244355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31687 q = 1) (hb : d241832 q = 1) : d244356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d244356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d244356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31690 q = 1) (hb : d241832 q = 1) : d244359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79164 q ha hb
    | true =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31691 q = 1) (hb : d241832 q = 1) : d244360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31692 q = 1) (hb : d241832 q = 1) : d244361 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31692, d244361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31692, d244361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31727 q = 1) (hb : d241832 q = 1) : d244396 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31727, d244396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31727, d244396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31728 q = 1) (hb : d241832 q = 1) : d244397 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31728, d244397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31728, d244397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31903 q = 1) (hb : d241832 q = 1) : d244451 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31903, d244451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31903, d244451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79197 (p : Pattern) (ha : d31904 p = 1) (hb : d241832 p = 1) : d244452 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31690 q = 1) (hb : d241832 q = 1) : d244359 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79164 q ha hb
    | true =>
      simp only [d31690, d244359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31691 q = 1) (hb : d241832 q = 1) : d244360 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31691, d244360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31696 q = 1) (hb : d241832 q = 1) : d244365 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31696, d244365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31696, d244365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31730 q = 1) (hb : d241832 q = 1) : d244399 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31730, d244399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31730, d244399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31731 q = 1) (hb : d241832 q = 1) : d244400 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31731, d244400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31731, d244400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31904 q = 1) (hb : d241832 q = 1) : d244452 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31904, d244452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31904, d244452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79198 (p : Pattern) (ha : d31908 p = 1) (hb : d241832 p = 1) : d244456 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31780 q = 1) (hb : d241832 q = 1) : d244418 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31780, d244418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79188 q ha hb
    | true =>
      simp only [d31780, d244418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31781 q = 1) (hb : d241832 q = 1) : d244419 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31781, d244419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31781, d244419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31686 q = 1) (hb : d241832 q = 1) : d244355 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31686, d244355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79163 q ha hb
    | true =>
      simp only [d31686, d244355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31687 q = 1) (hb : d241832 q = 1) : d244356 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31687, d244356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31687, d244356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31782 q = 1) (hb : d241832 q = 1) : d244420 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31782, d244420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31782, d244420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31783 q = 1) (hb : d241832 q = 1) : d244421 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31783, d244421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31783, d244421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31784 q = 1) (hb : d241832 q = 1) : d244422 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31784, d244422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31784, d244422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31908 q = 1) (hb : d241832 q = 1) : d244456 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31908, d244456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31908, d244456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79199 (p : Pattern) (ha : d31914 p = 1) (hb : d241832 p = 1) : d244459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31885 q = 1) (hb : d241832 q = 1) : d244433 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d31885, d244433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79191 q ha hb
    | true =>
      simp only [d31885, d244433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d31886 q = 1) (hb : d241832 q = 1) : d244434 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d31886, d244434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31886, d244434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31887 q = 1) (hb : d241832 q = 1) : d244435 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d31887, d244435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31887, d244435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31888 q = 1) (hb : d241832 q = 1) : d244436 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d31888, d244436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31888, d244436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31889 q = 1) (hb : d241832 q = 1) : d244437 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d31889, d244437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d31889, d244437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d31914 q = 1) (hb : d241832 q = 1) : d244459 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d31914, d244459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31914, d244459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79200 (p : Pattern) (ha : d241832 p = 1) (hb : d245517 p = 1) : d244465 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31723 q = 1) (hb : d241832 q = 1) : d244392 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31723, d244392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79179 q ha hb
    | true =>
      simp only [d31723, d244392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79180 q ha hb
  have h2 (q : Pattern) (ha : d31724 q = 1) (hb : d241832 q = 1) : d244393 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31724, d244393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31724, d244393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31725 q = 1) (hb : d241832 q = 1) : d244394 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31725, d244394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31725, d244394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31726 q = 1) (hb : d241832 q = 1) : d244395 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31726, d244395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31726, d244395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d31733 q = 1) (hb : d241832 q = 1) : d244402 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31733, d244402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79181 q ha hb
    | true =>
      simp only [d31733, d244402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79182 q ha hb
  have h6 (q : Pattern) (ha : d31734 q = 1) (hb : d241832 q = 1) : d244403 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31734, d244403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31734, d244403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31735 q = 1) (hb : d241832 q = 1) : d244404 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31735, d244404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31735, d244404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d31786 q = 1) (hb : d241832 q = 1) : d244424 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31786, d244424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79189 q ha hb
    | true =>
      simp only [d31786, d244424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79165 q ha hb
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d245508 q = 1) : d244425 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245508, d244425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d245508, d244425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d31891 q = 1) (hb : d241832 q = 1) : d244439 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31891, d244439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79192 q ha hb
    | true =>
      simp only [d31891, d244439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31892 q = 1) (hb : d241832 q = 1) : d244440 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31892, d244440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d31892, d244440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d241832 q = 1) (hb : d245509 q = 1) : d244441 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245509, d244441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d245509, d244441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d241832 q = 1) (hb : d245510 q = 1) : d244442 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245510, d244442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d245510, d244442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d245511 q = 1) : d244443 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245511, d244443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d245511, d244443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d31899 q = 1) (hb : d241832 q = 1) : d244447 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31899, d244447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79194 q ha hb
    | true =>
      simp only [d31899, d244447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79195 q ha hb
  have h16 (q : Pattern) (ha : d31900 q = 1) (hb : d241832 q = 1) : d244448 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31900, d244448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31900, d244448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d31901 q = 1) (hb : d241832 q = 1) : d244449 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31901, d244449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31901, d244449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d31902 q = 1) (hb : d241832 q = 1) : d244450 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d31902, d244450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31902, d244450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d31905 q = 1) (hb : d241832 q = 1) : d244453 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31905, d244453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79196 q ha hb
    | true =>
      simp only [d31905, d244453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79197 q ha hb
  have h20 (q : Pattern) (ha : d31906 q = 1) (hb : d241832 q = 1) : d244454 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31906, d244454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31906, d244454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d31907 q = 1) (hb : d241832 q = 1) : d244455 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d31907, d244455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d31907, d244455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d31909 q = 1) (hb : d241832 q = 1) : d244457 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31909, d244457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79198 q ha hb
    | true =>
      simp only [d31909, d244457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79168 q ha hb
  have h23 (q : Pattern) (ha : d241832 q = 1) (hb : d245513 q = 1) : d244458 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245513, d244458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d245513, d244458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d31915 q = 1) (hb : d241832 q = 1) : d244460 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31915, d244460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79199 q ha hb
    | true =>
      simp only [d31915, d244460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d31916 q = 1) (hb : d241832 q = 1) : d244461 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31916, d244461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d31916, d244461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d241832 q = 1) (hb : d245514 q = 1) : d244462 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245514, d244462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d245514, d244462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
  have h27 (q : Pattern) (ha : d241832 q = 1) (hb : d245515 q = 1) : d244463 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245515, d244463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
    | true =>
      simp only [d245515, d244463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d241832 q = 1) (hb : d245516 q = 1) : d244464 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245516, d244464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
    | true =>
      simp only [d245516, d244464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d241832 q = 1) (hb : d245517 q = 1) : d244465 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245517, d244465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245517, d244465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro79201 (p : Pattern) (ha : d241832 p = 1) (hb : d245524 p = 1) : d244485 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31909 q = 1) (hb : d241832 q = 1) : d244457 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31909, d244457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79198 q ha hb
    | true =>
      simp only [d31909, d244457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79168 q ha hb
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d245513 q = 1) : d244458 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245513, d244458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245513, d244458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d31915 q = 1) (hb : d241832 q = 1) : d244460 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d31915, d244460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79199 q ha hb
    | true =>
      simp only [d31915, d244460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d31916 q = 1) (hb : d241832 q = 1) : d244461 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d31916, d244461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31916, d244461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d245514 q = 1) : d244462 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245514, d244462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245514, d244462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d245522 q = 1) : d244483 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245522, d244483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245522, d244483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d245523 q = 1) : d244484 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245523, d244484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245523, d244484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d245524 q = 1) : d244485 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245524, d244485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245524, d244485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79202 (p : Pattern) (ha : d31966 p = 1) (hb : d241832 p = 1) : d244498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31948 q = 1) (hb : d241832 q = 1) : d244493 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31948, d244493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31948, d244493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79183 q ha hb
  have h2 (q : Pattern) (ha : d31743 q = 1) (hb : d241832 q = 1) : d244406 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31743, d244406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79183 q ha hb
    | true =>
      simp only [d31743, d244406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31949 q = 1) (hb : d241832 q = 1) : d244494 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31949, d244494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31949, d244494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31744 q = 1) (hb : d241832 q = 1) : d244407 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31744, d244407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31744, d244407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31950 q = 1) (hb : d241832 q = 1) : d244495 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31950, d244495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31950, d244495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31951 q = 1) (hb : d241832 q = 1) : d244496 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31951, d244496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31951, d244496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31952 q = 1) (hb : d241832 q = 1) : d31957 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31952, d31957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31952, d31957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79184 q ha hb
  have h8 (q : Pattern) (ha : d31748 q = 1) (hb : d241832 q = 1) : d31756 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31748, d31756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79184 q ha hb
    | true =>
      simp only [d31748, d31756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31953 q = 1) (hb : d241832 q = 1) : d31958 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31953, d31958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31953, d31958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31749 q = 1) (hb : d241832 q = 1) : d31757 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31749, d31757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31749, d31757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31954 q = 1) (hb : d241832 q = 1) : d31959 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31954, d31959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31954, d31959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31955 q = 1) (hb : d241832 q = 1) : d31960 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31955, d31960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31955, d31960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31956 q = 1) (hb : d241832 q = 1) : d244497 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31956, d244497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31956, d244497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31965 q = 1) (hb : d241832 q = 1) : d31965 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d31966 q = 1) (hb : d241832 q = 1) : d244498 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31966, d244498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31966, d244498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79203 (p : Pattern) (ha : d31981 p = 1) (hb : d241832 p = 1) : d244504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31967 q = 1) (hb : d241832 q = 1) : d31957 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31967, d31957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31967, d31957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79154 q ha hb
  have h2 (q : Pattern) (ha : d31627 q = 1) (hb : d241832 q = 1) : d31756 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31627, d31756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79154 q ha hb
    | true =>
      simp only [d31627, d31756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31968 q = 1) (hb : d241832 q = 1) : d31958 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31968, d31958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31968, d31958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31628 q = 1) (hb : d241832 q = 1) : d31757 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31628, d31757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31628, d31757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31969 q = 1) (hb : d241832 q = 1) : d31959 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31969, d31959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31969, d31959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31970 q = 1) (hb : d241832 q = 1) : d31960 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31970, d31960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31970, d31960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31971 q = 1) (hb : d241832 q = 1) : d31961 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31971, d31961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31971, d31961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79155 q ha hb
  have h8 (q : Pattern) (ha : d31637 q = 1) (hb : d241832 q = 1) : d31643 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31637, d31643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79155 q ha hb
    | true =>
      simp only [d31637, d31643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31972 q = 1) (hb : d241832 q = 1) : d31962 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31972, d31962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31972, d31962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31638 q = 1) (hb : d241832 q = 1) : d31644 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31638, d31644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31638, d31644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31973 q = 1) (hb : d241832 q = 1) : d31963 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31973, d31963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31973, d31963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31974 q = 1) (hb : d241832 q = 1) : d31964 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31974, d31964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31974, d31964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31975 q = 1) (hb : d241832 q = 1) : d31965 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31975, d31965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31975, d31965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31964 q = 1) (hb : d241832 q = 1) : d31964 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d31976 q = 1) (hb : d241832 q = 1) : d244499 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31976, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31976, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79156 q ha hb
  have h16 (q : Pattern) (ha : d31650 q = 1) (hb : d241832 q = 1) : d244336 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79156 q ha hb
    | true =>
      simp only [d31650, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d31977 q = 1) (hb : d241832 q = 1) : d244500 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31977, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d31977, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d31651 q = 1) (hb : d241832 q = 1) : d244337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d31651, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d31978 q = 1) (hb : d241832 q = 1) : d244501 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31978, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d31978, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d31979 q = 1) (hb : d241832 q = 1) : d244502 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31979, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d31979, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d31980 q = 1) (hb : d241832 q = 1) : d244503 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31980, d244503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d31980, d244503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d31981 q = 1) (hb : d241832 q = 1) : d244504 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31981, d244504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31981, d244504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  exact h22 p ha hb
theorem andIntro79204 (p : Pattern) (ha : d31991 p = 1) (hb : d241832 p = 1) : d244509 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31985 q = 1) (hb : d241832 q = 1) : d31961 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31985, d31961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31985, d31961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79186 q ha hb
  have h2 (q : Pattern) (ha : d31768 q = 1) (hb : d241832 q = 1) : d31643 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31768, d31643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79186 q ha hb
    | true =>
      simp only [d31768, d31643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31986 q = 1) (hb : d241832 q = 1) : d31962 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31986, d31962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31986, d31962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31769 q = 1) (hb : d241832 q = 1) : d31644 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31769, d31644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31769, d31644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31987 q = 1) (hb : d241832 q = 1) : d31963 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31987, d31963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31987, d31963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31988 q = 1) (hb : d241832 q = 1) : d31964 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31988, d31964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d31988, d31964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d31976 q = 1) (hb : d241832 q = 1) : d244499 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31976, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31976, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79156 q ha hb
  have h8 (q : Pattern) (ha : d31650 q = 1) (hb : d241832 q = 1) : d244336 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31650, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79156 q ha hb
    | true =>
      simp only [d31650, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d31977 q = 1) (hb : d241832 q = 1) : d244500 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31977, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d31977, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31651 q = 1) (hb : d241832 q = 1) : d244337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31651, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d31651, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d31978 q = 1) (hb : d241832 q = 1) : d244501 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d31978, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d31978, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d31979 q = 1) (hb : d241832 q = 1) : d244502 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d31979, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d31979, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d31989 q = 1) (hb : d241832 q = 1) : d244503 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31989, d244503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d31989, d244503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d31990 q = 1) (hb : d241832 q = 1) : d244508 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d31990, d244508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d31990, d244508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d31991 q = 1) (hb : d241832 q = 1) : d244509 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d31991, d244509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d31991, d244509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79205 (p : Pattern) (ha : d32016 p = 1) (hb : d241832 p = 1) : d244520 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31982 q = 1) (hb : d241832 q = 1) : d244505 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31982, d244505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79202 q ha hb
    | true =>
      simp only [d31982, d244505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79203 q ha hb
  have h2 (q : Pattern) (ha : d31983 q = 1) (hb : d241832 q = 1) : d244506 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31983, d244506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31983, d244506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d31984 q = 1) (hb : d241832 q = 1) : d244507 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31984, d244507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31984, d244507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31992 q = 1) (hb : d241832 q = 1) : d244510 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31992, d244510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79203 q ha hb
    | true =>
      simp only [d31992, d244510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79204 q ha hb
  have h5 (q : Pattern) (ha : d31993 q = 1) (hb : d241832 q = 1) : d244511 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d31993, d244511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31993, d244511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d31994 q = 1) (hb : d241832 q = 1) : d244512 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d31994, d244512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31994, d244512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d31995 q = 1) (hb : d241832 q = 1) : d244513 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d31995, d244513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31995, d244513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32006 q = 1) (hb : d241832 q = 1) : d244510 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32006, d244510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79203 q ha hb
    | true =>
      simp only [d32006, d244510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79174 q ha hb
  have h9 (q : Pattern) (ha : d32007 q = 1) (hb : d241832 q = 1) : d244511 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32007, d244511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32007, d244511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32008 q = 1) (hb : d241832 q = 1) : d244512 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32008, d244512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32008, d244512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32011 q = 1) (hb : d241832 q = 1) : d244515 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32011, d244515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79174 q ha hb
    | true =>
      simp only [d32011, d244515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79175 q ha hb
  have h12 (q : Pattern) (ha : d32012 q = 1) (hb : d241832 q = 1) : d244516 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32012, d244516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32012, d244516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32013 q = 1) (hb : d241832 q = 1) : d244517 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32013, d244517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32013, d244517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d32014 q = 1) (hb : d241832 q = 1) : d244518 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32014, d244518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32014, d244518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d32015 q = 1) (hb : d241832 q = 1) : d244519 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32015, d244519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32015, d244519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d32016 q = 1) (hb : d241832 q = 1) : d244520 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32016, d244520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32016, d244520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h16 p ha hb
theorem andIntro79206 (p : Pattern) (ha : d32021 p = 1) (hb : d241832 p = 1) : d244525 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32006 q = 1) (hb : d241832 q = 1) : d244510 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32006, d244510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79203 q ha hb
    | true =>
      simp only [d32006, d244510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79174 q ha hb
  have h2 (q : Pattern) (ha : d32007 q = 1) (hb : d241832 q = 1) : d244511 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32007, d244511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32007, d244511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32008 q = 1) (hb : d241832 q = 1) : d244512 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32008, d244512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32008, d244512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32011 q = 1) (hb : d241832 q = 1) : d244515 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32011, d244515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79174 q ha hb
    | true =>
      simp only [d32011, d244515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79175 q ha hb
  have h5 (q : Pattern) (ha : d32012 q = 1) (hb : d241832 q = 1) : d244516 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32012, d244516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32012, d244516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32013 q = 1) (hb : d241832 q = 1) : d244517 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32013, d244517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32013, d244517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32014 q = 1) (hb : d241832 q = 1) : d244518 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32014, d244518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32014, d244518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32019 q = 1) (hb : d241832 q = 1) : d244523 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32019, d244523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32019, d244523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32020 q = 1) (hb : d241832 q = 1) : d244524 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32020, d244524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32020, d244524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32021 q = 1) (hb : d241832 q = 1) : d244525 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32021, d244525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32021, d244525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro79207 (p : Pattern) (ha : d32027 p = 1) (hb : d241832 p = 1) : d244531 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32017 q = 1) (hb : d241832 q = 1) : d244521 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32017, d244521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79205 q ha hb
    | true =>
      simp only [d32017, d244521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32018 q = 1) (hb : d241832 q = 1) : d244522 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32018, d244522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32018, d244522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32022 q = 1) (hb : d241832 q = 1) : d244526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32022, d244526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79206 q ha hb
    | true =>
      simp only [d32022, d244526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32023 q = 1) (hb : d241832 q = 1) : d244527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32023, d244527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32023, d244527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32024 q = 1) (hb : d241832 q = 1) : d244528 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32024, d244528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32024, d244528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32025 q = 1) (hb : d241832 q = 1) : d244529 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32025, d244529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32025, d244529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32026 q = 1) (hb : d241832 q = 1) : d244530 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32026, d244530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32026, d244530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32027 q = 1) (hb : d241832 q = 1) : d244531 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32027, d244531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32027, d244531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79208 (p : Pattern) (ha : d32035 p = 1) (hb : d241832 p = 1) : d244539 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32022 q = 1) (hb : d241832 q = 1) : d244526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32022, d244526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79206 q ha hb
    | true =>
      simp only [d32022, d244526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32023 q = 1) (hb : d241832 q = 1) : d244527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32023, d244527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32023, d244527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32030 q = 1) (hb : d241832 q = 1) : d244534 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32030, d244534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79176 q ha hb
    | true =>
      simp only [d32030, d244534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32031 q = 1) (hb : d241832 q = 1) : d244535 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32031, d244535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32031, d244535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32032 q = 1) (hb : d241832 q = 1) : d244536 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32032, d244536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32032, d244536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32033 q = 1) (hb : d241832 q = 1) : d244537 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32033, d244537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32033, d244537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32034 q = 1) (hb : d241832 q = 1) : d244538 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32034, d244538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32034, d244538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32035 q = 1) (hb : d241832 q = 1) : d244539 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32035, d244539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32035, d244539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79209 (p : Pattern) (ha : d32095 p = 1) (hb : d241832 p = 1) : d244542 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32000 q = 1) (hb : d241832 q = 1) : d244499 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32000, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32000, d244499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79159 q ha hb
  have h2 (q : Pattern) (ha : d31667 q = 1) (hb : d241832 q = 1) : d244336 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d31667, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79159 q ha hb
    | true =>
      simp only [d31667, d244336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32001 q = 1) (hb : d241832 q = 1) : d244500 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32001, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32001, d244500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31668 q = 1) (hb : d241832 q = 1) : d244337 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d31668, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31668, d244337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32002 q = 1) (hb : d241832 q = 1) : d244501 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32002, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32002, d244501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32003 q = 1) (hb : d241832 q = 1) : d244502 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32003, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32003, d244502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32009 q = 1) (hb : d241832 q = 1) : d244508 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32009, d244508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32009, d244508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32095 q = 1) (hb : d241832 q = 1) : d244542 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32095, d244542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32095, d244542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79210 (p : Pattern) (ha : d32101 p = 1) (hb : d241832 p = 1) : d244548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32006 q = 1) (hb : d241832 q = 1) : d244510 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32006, d244510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79203 q ha hb
    | true =>
      simp only [d32006, d244510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79174 q ha hb
  have h2 (q : Pattern) (ha : d32007 q = 1) (hb : d241832 q = 1) : d244511 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32007, d244511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32007, d244511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32008 q = 1) (hb : d241832 q = 1) : d244512 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32008, d244512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32008, d244512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32011 q = 1) (hb : d241832 q = 1) : d244515 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32011, d244515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79174 q ha hb
    | true =>
      simp only [d32011, d244515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79175 q ha hb
  have h5 (q : Pattern) (ha : d32012 q = 1) (hb : d241832 q = 1) : d244516 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32012, d244516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32012, d244516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32013 q = 1) (hb : d241832 q = 1) : d244517 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32013, d244517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32013, d244517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32014 q = 1) (hb : d241832 q = 1) : d244518 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32014, d244518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32014, d244518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32096 q = 1) (hb : d241832 q = 1) : d244543 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32096, d244543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79174 q ha hb
    | true =>
      simp only [d32096, d244543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79209 q ha hb
  have h9 (q : Pattern) (ha : d32097 q = 1) (hb : d241832 q = 1) : d244544 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32097, d244544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32097, d244544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32098 q = 1) (hb : d241832 q = 1) : d244545 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32098, d244545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32098, d244545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32099 q = 1) (hb : d241832 q = 1) : d244546 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32099, d244546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32099, d244546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d32100 q = 1) (hb : d241832 q = 1) : d244547 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32100, d244547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32100, d244547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32101 q = 1) (hb : d241832 q = 1) : d244548 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32101, d244548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32101, d244548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro79211 (p : Pattern) (ha : d32107 p = 1) (hb : d241832 p = 1) : d244554 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32102 q = 1) (hb : d241832 q = 1) : d244549 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32102, d244549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79210 q ha hb
    | true =>
      simp only [d32102, d244549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32103 q = 1) (hb : d241832 q = 1) : d244550 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32103, d244550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32103, d244550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32104 q = 1) (hb : d241832 q = 1) : d244551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32104, d244551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32104, d244551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32105 q = 1) (hb : d241832 q = 1) : d244552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32105, d244552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32105, d244552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32106 q = 1) (hb : d241832 q = 1) : d244553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32106, d244553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32106, d244553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32107 q = 1) (hb : d241832 q = 1) : d244554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32107, d244554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32107, d244554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79212 (p : Pattern) (ha : d241832 p = 1) (hb : d245534 p = 1) : d244560 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32036 q = 1) (hb : d241832 q = 1) : d244540 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32036, d244540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79207 q ha hb
    | true =>
      simp only [d32036, d244540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79208 q ha hb
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d245530 q = 1) : d244541 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d245530, d244541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d245530, d244541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d32108 q = 1) (hb : d241832 q = 1) : d244555 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32108, d244555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79211 q ha hb
    | true =>
      simp only [d32108, d244555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32109 q = 1) (hb : d241832 q = 1) : d244556 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32109, d244556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32109, d244556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d245531 q = 1) : d244557 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d245531, d244557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d245531, d244557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d245532 q = 1) : d244558 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d245532, d244558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245532, d244558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d241832 q = 1) (hb : d245533 q = 1) : d244559 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d245533, d244559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245533, d244559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d245534 q = 1) : d244560 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d245534, d244560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245534, d244560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79213 (p : Pattern) (ha : d241832 p = 1) (hb : d245540 p = 1) : d244577 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31706 q = 1) (hb : d241832 q = 1) : d244375 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31706, d244375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31706, d244375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79167 q ha hb
  have h2 (q : Pattern) (ha : d31707 q = 1) (hb : d241832 q = 1) : d244376 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d31707, d244376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d31707, d244376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d31716 q = 1) (hb : d241832 q = 1) : d244385 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31716, d244385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79167 q ha hb
    | true =>
      simp only [d31716, d244385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79170 q ha hb
  have h4 (q : Pattern) (ha : d31717 q = 1) (hb : d241832 q = 1) : d244386 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d31717, d244386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d31717, d244386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d31718 q = 1) (hb : d241832 q = 1) : d244387 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d31718, d244387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d31718, d244387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d245518 q = 1) : d244466 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245518, d244466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79193 q ha hb
    | true =>
      simp only [d245518, d244466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79200 q ha hb
  have h7 (q : Pattern) (ha : d31934 q = 1) (hb : d241832 q = 1) : d244479 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31934, d244479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79171 q ha hb
    | true =>
      simp only [d31934, d244479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79172 q ha hb
  have h8 (q : Pattern) (ha : d241832 q = 1) (hb : d245519 q = 1) : d244480 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245519, d244480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d245519, d244480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d241832 q = 1) (hb : d245520 q = 1) : d244481 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245520, d244481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d245520, d244481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d241832 q = 1) (hb : d245521 q = 1) : d244482 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245521, d244482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d245521, d244482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d241832 q = 1) (hb : d245525 q = 1) : d244486 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245525, d244486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245525, d244486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79201 q ha hb
  have h12 (q : Pattern) (ha : d31943 q = 1) (hb : d241832 q = 1) : d244488 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d31943, d244488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d31943, d244488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79173 q ha hb
  have h13 (q : Pattern) (ha : d241832 q = 1) (hb : d245526 q = 1) : d244489 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245526, d244489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d245526, d244489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d241832 q = 1) (hb : d245527 q = 1) : d244490 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245527, d244490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d245527, d244490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d241832 q = 1) (hb : d245528 q = 1) : d244491 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245528, d244491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d245528, d244491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d241832 q = 1) (hb : d245529 q = 1) : d244492 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245529, d244492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d245529, d244492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d241832 q = 1) (hb : d245535 q = 1) : d244561 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d245535, d244561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245535, d244561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79212 q ha hb
  have h18 (q : Pattern) (ha : d32125 q = 1) (hb : d241832 q = 1) : d244572 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d32125, d244572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32125, d244572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79178 q ha hb
  have h19 (q : Pattern) (ha : d241832 q = 1) (hb : d245536 q = 1) : d244573 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d245536, d244573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d245536, d244573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d241832 q = 1) (hb : d245537 q = 1) : d244574 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d245537, d244574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d245537, d244574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d241832 q = 1) (hb : d245538 q = 1) : d244575 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d245538, d244575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d245538, d244575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d241832 q = 1) (hb : d245539 q = 1) : d244576 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d245539, d244576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d245539, d244576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d241832 q = 1) (hb : d245540 q = 1) : d244577 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d245540, d244577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d245540, d244577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro79214 (p : Pattern) (ha : d241832 p = 1) (hb : d245546 p = 1) : d244583 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d241832 q = 1) (hb : d245541 q = 1) : d244578 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d245541, d244578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245541, d244578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79213 q ha hb
  have h2 (q : Pattern) (ha : d241832 q = 1) (hb : d245542 q = 1) : d244579 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d245542, d244579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245542, d244579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d241832 q = 1) (hb : d245543 q = 1) : d244580 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d245543, d244580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245543, d244580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d241832 q = 1) (hb : d245544 q = 1) : d244581 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d245544, d244581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245544, d244581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d241832 q = 1) (hb : d245545 q = 1) : d244582 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d245545, d244582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245545, d244582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d241832 q = 1) (hb : d245546 q = 1) : d244583 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d245546, d244583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d245546, d244583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79215 (p : Pattern) (ha : d32146 p = 1) (hb : d241832 p = 1) : d32273 p = 1 := by
  have h0 (q : Pattern) (ha : d31738 q = 1) (hb : d241832 q = 1) : d31738 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31304 q = 1) (hb : d202304 q = 1) : d31304 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d10054 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d32141 q = 1) (hb : d241830 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32141, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32141, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d32142 q = 1) (hb : d241830 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32143 q = 1) (hb : d241831 q = 1) : d32168 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32143, d241831, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32143, d241831, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d31739 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d32144 q = 1) (hb : d241832 q = 1) : d32169 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32144, d241832, d32169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32144, d241832, d32169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d32145 q = 1) (hb : d241832 q = 1) : d32170 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32145, d32170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32145, d32170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32146 q = 1) (hb : d241832 q = 1) : d32273 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32146, d32273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32146, d32273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro79216 (p : Pattern) (ha : d32160 p = 1) (hb : d241832 p = 1) : d32171 p = 1 := by
  have h0 (q : Pattern) (ha : d31304 q = 1) (hb : d202304 q = 1) : d31304 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10054 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32141 q = 1) (hb : d241830 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32141, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32141, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d32142 q = 1) (hb : d241830 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32143 q = 1) (hb : d241831 q = 1) : d32168 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32143, d241831, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32143, d241831, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d31306 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d32151 q = 1) (hb : d241832 q = 1) : d32169 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32151, d241832, d32169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32151, d241832, d32169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d32152 q = 1) (hb : d241832 q = 1) : d32170 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32152, d32170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32152, d32170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32159 q = 1) (hb : d241832 q = 1) : d32159 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d32160 q = 1) (hb : d241832 q = 1) : d32171 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32160, d32171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32160, d32171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro79217 (p : Pattern) (ha : d32180 p = 1) (hb : d241832 p = 1) : d244587 p = 1 := by
  have h0 (q : Pattern) (ha : d32157 q = 1) (hb : d241831 q = 1) : d32157 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25767 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32176 q = 1) (hb : d241832 q = 1) : d32158 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32176, d241832, d32158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32176, d241832, d32158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d32177 q = 1) (hb : d241832 q = 1) : d32159 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32177, d32159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32177, d32159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1577 q = 1) (hb : d241831 q = 1) : d1577 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d10131 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d32178 q = 1) (hb : d241832 q = 1) : d24324 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32178, d241832, d24324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32178, d241832, d24324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d32179 q = 1) (hb : d241832 q = 1) : d24325 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32179, d24325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32179, d24325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d32180 q = 1) (hb : d241832 q = 1) : d244587 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32180, d244587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32180, d244587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro79218 (p : Pattern) (ha : d32186 p = 1) (hb : d241832 p = 1) : d244593 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32147 q = 1) (hb : d241832 q = 1) : d32274 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32147, d32274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79215 q ha hb
    | true =>
      simp only [d32147, d32274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32148 q = 1) (hb : d241832 q = 1) : d32275 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32148, d32275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32148, d32275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32149 q = 1) (hb : d241832 q = 1) : d32276 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32149, d32276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32149, d32276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32150 q = 1) (hb : d241832 q = 1) : d32277 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32150, d32277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32150, d32277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32161 q = 1) (hb : d241832 q = 1) : d32172 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32161, d32172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79216 q ha hb
    | true =>
      simp only [d32161, d32172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32162 q = 1) (hb : d241832 q = 1) : d32173 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32162, d32173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32162, d32173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32163 q = 1) (hb : d241832 q = 1) : d32174 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32163, d32174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32163, d32174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32164 q = 1) (hb : d241832 q = 1) : d32175 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32164, d32175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32164, d32175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32165 q = 1) (hb : d241832 q = 1) : d32279 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32165, d32279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32165, d32279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32175 q = 1) (hb : d241832 q = 1) : d32175 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d32181 q = 1) (hb : d241832 q = 1) : d244588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32181, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79217 q ha hb
    | true =>
      simp only [d32181, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d32182 q = 1) (hb : d241832 q = 1) : d244589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32182, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32182, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d32183 q = 1) (hb : d241832 q = 1) : d244590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32183, d244590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32183, d244590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d32184 q = 1) (hb : d241832 q = 1) : d244591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32184, d244591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32184, d244591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d32185 q = 1) (hb : d241832 q = 1) : d244592 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32185, d244592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32185, d244592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d32186 q = 1) (hb : d241832 q = 1) : d244593 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32186, d244593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32186, d244593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro79219 (p : Pattern) (ha : d32193 p = 1) (hb : d241832 p = 1) : d32171 p = 1 := by
  have h0 (q : Pattern) (ha : d31304 q = 1) (hb : d202304 q = 1) : d31304 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10054 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32141 q = 1) (hb : d241830 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32141, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32141, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d32142 q = 1) (hb : d241830 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32143 q = 1) (hb : d241831 q = 1) : d32168 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32143, d241831, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32143, d241831, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d31306 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d32151 q = 1) (hb : d241832 q = 1) : d32169 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32151, d241832, d32169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32151, d241832, d32169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d32152 q = 1) (hb : d241832 q = 1) : d32170 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32152, d32170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32152, d32170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32156 q = 1) (hb : d202304 q = 1) : d32156 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d25764 q = 1) (hb : d202304 q = 1) : d25764 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d1563 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d32187 q = 1) (hb : d241830 q = 1) : d25765 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32187, d241830, d25765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32187, d241830, d25765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d32188 q = 1) (hb : d241830 q = 1) : d25766 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32188, d25766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32188, d25766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d32189 q = 1) (hb : d241831 q = 1) : d32157 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32189, d241831, d32157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32189, d241831, d32157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d32190 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d32191 q = 1) (hb : d241832 q = 1) : d32158 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32191, d241832, d32158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d32191, d241832, d32158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d32192 q = 1) (hb : d241832 q = 1) : d32159 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32192, d32159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d32192, d32159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h20 (q : Pattern) (ha : d32193 q = 1) (hb : d241832 q = 1) : d32171 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32193, d32171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32193, d32171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  exact h20 p ha hb
theorem andIntro79220 (p : Pattern) (ha : d32198 p = 1) (hb : d241832 p = 1) : d244587 p = 1 := by
  have h0 (q : Pattern) (ha : d32156 q = 1) (hb : d202304 q = 1) : d32156 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d25764 q = 1) (hb : d202304 q = 1) : d25764 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1563 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32187 q = 1) (hb : d241830 q = 1) : d25765 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32187, d241830, d25765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32187, d241830, d25765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d32188 q = 1) (hb : d241830 q = 1) : d25766 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32188, d25766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32188, d25766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32189 q = 1) (hb : d241831 q = 1) : d32157 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32189, d241831, d32157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32189, d241831, d32157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d32190 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d32191 q = 1) (hb : d241832 q = 1) : d32158 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32191, d241832, d32158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32191, d241832, d32158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d32192 q = 1) (hb : d241832 q = 1) : d32159 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32192, d32159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32192, d32159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1577 q = 1) (hb : d241831 q = 1) : d1577 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d10131 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d32178 q = 1) (hb : d241832 q = 1) : d24324 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32178, d241832, d24324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32178, d241832, d24324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d32179 q = 1) (hb : d241832 q = 1) : d24325 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32179, d24325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32179, d24325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h15 (q : Pattern) (ha : d32198 q = 1) (hb : d241832 q = 1) : d244587 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32198, d244587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32198, d244587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79221 (p : Pattern) (ha : d32205 p = 1) (hb : d241832 p = 1) : d244595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32194 q = 1) (hb : d241832 q = 1) : d32172 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32194, d32172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79219 q ha hb
    | true =>
      simp only [d32194, d32172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32195 q = 1) (hb : d241832 q = 1) : d32173 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32195, d32173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32195, d32173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32196 q = 1) (hb : d241832 q = 1) : d32174 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32196, d32174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32196, d32174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32197 q = 1) (hb : d241832 q = 1) : d32175 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32197, d32175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32197, d32175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32199 q = 1) (hb : d241832 q = 1) : d244588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32199, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79220 q ha hb
    | true =>
      simp only [d32199, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32200 q = 1) (hb : d241832 q = 1) : d244589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32200, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32200, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32201 q = 1) (hb : d241832 q = 1) : d244590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32201, d244590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32201, d244590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32202 q = 1) (hb : d241832 q = 1) : d244591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32202, d244591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32202, d244591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32203 q = 1) (hb : d241832 q = 1) : d244592 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32203, d244592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32203, d244592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32181 q = 1) (hb : d241832 q = 1) : d244588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32181, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79217 q ha hb
    | true =>
      simp only [d32181, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32182 q = 1) (hb : d241832 q = 1) : d244589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32182, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32182, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d32183 q = 1) (hb : d241832 q = 1) : d244590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32183, d244590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32183, d244590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32184 q = 1) (hb : d241832 q = 1) : d244591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32184, d244591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32184, d244591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d32204 q = 1) (hb : d241832 q = 1) : d244594 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32204, d244594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32204, d244594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d32205 q = 1) (hb : d241832 q = 1) : d244595 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32205, d244595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32205, d244595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79222 (p : Pattern) (ha : d10134 p = 1) (hb : d241832 p = 1) : d1596 p = 1 := by
  have h0 (q : Pattern) (ha : d1593 q = 1) (hb : d241831 q = 1) : d1593 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10131 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10132 q = 1) (hb : d241832 q = 1) : d1594 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10132, d241832, d1594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10132, d241832, d1594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d10133 q = 1) (hb : d241832 q = 1) : d1595 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10133, d1595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10133, d1595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10134 q = 1) (hb : d241832 q = 1) : d1596 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d10134, d1596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10134, d1596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h5 p ha hb
theorem andIntro79223 (p : Pattern) (ha : d32210 p = 1) (hb : d241832 p = 1) : d244599 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32199 q = 1) (hb : d241832 q = 1) : d244588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32199, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79220 q ha hb
    | true =>
      simp only [d32199, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32200 q = 1) (hb : d241832 q = 1) : d244589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32200, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32200, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32201 q = 1) (hb : d241832 q = 1) : d244590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32201, d244590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32201, d244590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32202 q = 1) (hb : d241832 q = 1) : d244591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32202, d244591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32202, d244591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32209 q = 1) (hb : d241832 q = 1) : d244594 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32209, d244594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32209, d244594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10135 q = 1) (hb : d241832 q = 1) : d1597 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d1597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79222 q ha hb
    | true =>
      simp only [d10135, d1597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10137 q = 1) (hb : d241832 q = 1) : d1598 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d1598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10137, d1598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15163 q = 1) (hb : d241832 q = 1) : d1599 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, d1599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15163, d1599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15164 q = 1) (hb : d241832 q = 1) : d1600 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, d1600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15164, d1600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15165 q = 1) (hb : d241832 q = 1) : d1601 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15165, d1601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15165, d1601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32210 q = 1) (hb : d241832 q = 1) : d244599 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32210, d244599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32210, d244599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79224 (p : Pattern) (ha : d32217 p = 1) (hb : d241832 p = 1) : d244606 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32206 q = 1) (hb : d241832 q = 1) : d244596 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32206, d244596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79218 q ha hb
    | true =>
      simp only [d32206, d244596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79221 q ha hb
  have h2 (q : Pattern) (ha : d32207 q = 1) (hb : d241832 q = 1) : d244597 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32207, d244597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32207, d244597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32208 q = 1) (hb : d241832 q = 1) : d244598 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32208, d244598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32208, d244598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32211 q = 1) (hb : d241832 q = 1) : d244600 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32211, d244600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79221 q ha hb
    | true =>
      simp only [d32211, d244600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79223 q ha hb
  have h5 (q : Pattern) (ha : d32212 q = 1) (hb : d241832 q = 1) : d244601 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32212, d244601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32212, d244601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32213 q = 1) (hb : d241832 q = 1) : d244602 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32213, d244602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32213, d244602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32214 q = 1) (hb : d241832 q = 1) : d244603 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32214, d244603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32214, d244603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32215 q = 1) (hb : d241832 q = 1) : d244604 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32215, d244604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32215, d244604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32216 q = 1) (hb : d241832 q = 1) : d244605 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32216, d244605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32216, d244605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32217 q = 1) (hb : d241832 q = 1) : d244606 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32217, d244606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32217, d244606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro79225 (p : Pattern) (ha : d32221 p = 1) (hb : d241832 p = 1) : d244610 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32211 q = 1) (hb : d241832 q = 1) : d244600 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32211, d244600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79221 q ha hb
    | true =>
      simp only [d32211, d244600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79223 q ha hb
  have h2 (q : Pattern) (ha : d32212 q = 1) (hb : d241832 q = 1) : d244601 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32212, d244601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32212, d244601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32213 q = 1) (hb : d241832 q = 1) : d244602 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32213, d244602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32213, d244602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32215 q = 1) (hb : d241832 q = 1) : d244604 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32215, d244604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32215, d244604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32220 q = 1) (hb : d241832 q = 1) : d244609 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32220, d244609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32220, d244609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32221 q = 1) (hb : d241832 q = 1) : d244610 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32221, d244610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32221, d244610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79226 (p : Pattern) (ha : d32227 p = 1) (hb : d241832 p = 1) : d244616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32218 q = 1) (hb : d241832 q = 1) : d244607 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32218, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79224 q ha hb
    | true =>
      simp only [d32218, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32219 q = 1) (hb : d241832 q = 1) : d244608 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32219, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32219, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32222 q = 1) (hb : d241832 q = 1) : d244611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79225 q ha hb
    | true =>
      simp only [d32222, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32223 q = 1) (hb : d241832 q = 1) : d244612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32224 q = 1) (hb : d241832 q = 1) : d244613 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32224, d244613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32224, d244613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32225 q = 1) (hb : d241832 q = 1) : d244614 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32225, d244614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32225, d244614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32226 q = 1) (hb : d241832 q = 1) : d244615 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32226, d244615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32226, d244615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32227 q = 1) (hb : d241832 q = 1) : d244616 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32227, d244616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32227, d244616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79227 (p : Pattern) (ha : d32231 p = 1) (hb : d241832 p = 1) : d244620 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32222 q = 1) (hb : d241832 q = 1) : d244611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79225 q ha hb
    | true =>
      simp only [d32222, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32223 q = 1) (hb : d241832 q = 1) : d244612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32228 q = 1) (hb : d241832 q = 1) : d244617 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32228, d244617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32228, d244617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32229 q = 1) (hb : d241832 q = 1) : d244618 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32229, d244618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32229, d244618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32230 q = 1) (hb : d241832 q = 1) : d244619 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32230, d244619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32230, d244619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32231 q = 1) (hb : d241832 q = 1) : d244620 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32231, d244620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32231, d244620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79228 (p : Pattern) (ha : d32237 p = 1) (hb : d241832 p = 1) : d244626 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32232 q = 1) (hb : d241832 q = 1) : d244621 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32232, d244621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79226 q ha hb
    | true =>
      simp only [d32232, d244621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79227 q ha hb
  have h2 (q : Pattern) (ha : d32233 q = 1) (hb : d241832 q = 1) : d244622 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32233, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32233, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32234 q = 1) (hb : d241832 q = 1) : d244623 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32234, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32234, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32235 q = 1) (hb : d241832 q = 1) : d244624 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32235, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32235, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32236 q = 1) (hb : d241832 q = 1) : d244625 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32236, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32236, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32237 q = 1) (hb : d241832 q = 1) : d244626 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32237, d244626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32237, d244626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79229 (p : Pattern) (ha : d32240 p = 1) (hb : d241832 p = 1) : d244629 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32218 q = 1) (hb : d241832 q = 1) : d244607 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32218, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79224 q ha hb
    | true =>
      simp only [d32218, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32219 q = 1) (hb : d241832 q = 1) : d244608 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32219, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32219, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32222 q = 1) (hb : d241832 q = 1) : d244611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79225 q ha hb
    | true =>
      simp only [d32222, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32223 q = 1) (hb : d241832 q = 1) : d244612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32224 q = 1) (hb : d241832 q = 1) : d244613 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32224, d244613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32224, d244613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32225 q = 1) (hb : d241832 q = 1) : d244614 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32225, d244614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32225, d244614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32226 q = 1) (hb : d241832 q = 1) : d244615 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32226, d244615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32226, d244615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32240 q = 1) (hb : d241832 q = 1) : d244629 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32240, d244629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32240, d244629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro79230 (p : Pattern) (ha : d32241 p = 1) (hb : d241832 p = 1) : d244630 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32222 q = 1) (hb : d241832 q = 1) : d244611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79225 q ha hb
    | true =>
      simp only [d32222, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32223 q = 1) (hb : d241832 q = 1) : d244612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32228 q = 1) (hb : d241832 q = 1) : d244617 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32228, d244617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32228, d244617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32229 q = 1) (hb : d241832 q = 1) : d244618 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32229, d244618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32229, d244618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32230 q = 1) (hb : d241832 q = 1) : d244619 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32230, d244619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32230, d244619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32241 q = 1) (hb : d241832 q = 1) : d244630 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32241, d244630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32241, d244630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79231 (p : Pattern) (ha : d32247 p = 1) (hb : d241832 p = 1) : d244636 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32232 q = 1) (hb : d241832 q = 1) : d244621 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32232, d244621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79226 q ha hb
    | true =>
      simp only [d32232, d244621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79227 q ha hb
  have h2 (q : Pattern) (ha : d32233 q = 1) (hb : d241832 q = 1) : d244622 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32233, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32233, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32234 q = 1) (hb : d241832 q = 1) : d244623 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32234, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32234, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32235 q = 1) (hb : d241832 q = 1) : d244624 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32235, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32235, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32236 q = 1) (hb : d241832 q = 1) : d244625 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32236, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32236, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32242 q = 1) (hb : d241832 q = 1) : d244631 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32242, d244631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79229 q ha hb
    | true =>
      simp only [d32242, d244631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79230 q ha hb
  have h7 (q : Pattern) (ha : d32243 q = 1) (hb : d241832 q = 1) : d244632 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32243, d244632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32243, d244632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32244 q = 1) (hb : d241832 q = 1) : d244633 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32244, d244633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32244, d244633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32245 q = 1) (hb : d241832 q = 1) : d244634 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32245, d244634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32245, d244634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32246 q = 1) (hb : d241832 q = 1) : d244635 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32246, d244635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32246, d244635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32247 q = 1) (hb : d241832 q = 1) : d244636 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32247, d244636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32247, d244636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79232 (p : Pattern) (ha : d32466 p = 1) (hb : d241832 p = 1) : d244724 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32232 q = 1) (hb : d241832 q = 1) : d244621 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32232, d244621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79226 q ha hb
    | true =>
      simp only [d32232, d244621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79227 q ha hb
  have h2 (q : Pattern) (ha : d32233 q = 1) (hb : d241832 q = 1) : d244622 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32233, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32233, d244622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32234 q = 1) (hb : d241832 q = 1) : d244623 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32234, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32234, d244623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32235 q = 1) (hb : d241832 q = 1) : d244624 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32235, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32235, d244624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32236 q = 1) (hb : d241832 q = 1) : d244625 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32236, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32236, d244625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32461 q = 1) (hb : d241832 q = 1) : d244719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32461, d244719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79227 q ha hb
    | true =>
      simp only [d32461, d244719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32462 q = 1) (hb : d241832 q = 1) : d244720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32462, d244720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32462, d244720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32463 q = 1) (hb : d241832 q = 1) : d244721 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32463, d244721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32463, d244721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32464 q = 1) (hb : d241832 q = 1) : d244722 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32464, d244722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32464, d244722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32465 q = 1) (hb : d241832 q = 1) : d244723 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32465, d244723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32465, d244723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32466 q = 1) (hb : d241832 q = 1) : d244724 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32466, d244724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32466, d244724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79233 (p : Pattern) (ha : d32472 p = 1) (hb : d241832 p = 1) : d244730 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32461 q = 1) (hb : d241832 q = 1) : d244719 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32461, d244719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79227 q ha hb
    | true =>
      simp only [d32461, d244719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32462 q = 1) (hb : d241832 q = 1) : d244720 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32462, d244720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32462, d244720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32463 q = 1) (hb : d241832 q = 1) : d244721 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32463, d244721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32463, d244721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32464 q = 1) (hb : d241832 q = 1) : d244722 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32464, d244722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32464, d244722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32465 q = 1) (hb : d241832 q = 1) : d244723 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32465, d244723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32465, d244723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32467 q = 1) (hb : d241832 q = 1) : d244725 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32467, d244725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79230 q ha hb
    | true =>
      simp only [d32467, d244725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32468 q = 1) (hb : d241832 q = 1) : d244726 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32468, d244726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32468, d244726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32469 q = 1) (hb : d241832 q = 1) : d244727 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32469, d244727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32469, d244727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32470 q = 1) (hb : d241832 q = 1) : d244728 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32470, d244728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32470, d244728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32471 q = 1) (hb : d241832 q = 1) : d244729 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32471, d244729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32471, d244729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32472 q = 1) (hb : d241832 q = 1) : d244730 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32472, d244730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32472, d244730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79234 (p : Pattern) (ha : d32481 p = 1) (hb : d241832 p = 1) : d244739 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32467 q = 1) (hb : d241832 q = 1) : d244725 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32467, d244725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79230 q ha hb
    | true =>
      simp only [d32467, d244725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32468 q = 1) (hb : d241832 q = 1) : d244726 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32468, d244726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32468, d244726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32469 q = 1) (hb : d241832 q = 1) : d244727 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32469, d244727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32469, d244727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32470 q = 1) (hb : d241832 q = 1) : d244728 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32470, d244728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32470, d244728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32471 q = 1) (hb : d241832 q = 1) : d244729 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32471, d244729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32471, d244729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32481 q = 1) (hb : d241832 q = 1) : d244739 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32481, d244739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32481, d244739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79235 (p : Pattern) (ha : d32540 p = 1) (hb : d241832 p = 1) : d244755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32531 q = 1) (hb : d241832 q = 1) : d32496 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32531, d32496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32531, d32496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79219 q ha hb
  have h2 (q : Pattern) (ha : d32194 q = 1) (hb : d241832 q = 1) : d32172 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32194, d32172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79219 q ha hb
    | true =>
      simp only [d32194, d32172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32532 q = 1) (hb : d241832 q = 1) : d32497 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32532, d32497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32532, d32497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32195 q = 1) (hb : d241832 q = 1) : d32173 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32195, d32173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32195, d32173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32533 q = 1) (hb : d241832 q = 1) : d32498 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32533, d32498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32533, d32498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32534 q = 1) (hb : d241832 q = 1) : d32499 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32534, d32499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32534, d32499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32535 q = 1) (hb : d241832 q = 1) : d244745 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32535, d244745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32535, d244745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79220 q ha hb
  have h8 (q : Pattern) (ha : d32199 q = 1) (hb : d241832 q = 1) : d244588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32199, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79220 q ha hb
    | true =>
      simp only [d32199, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32536 q = 1) (hb : d241832 q = 1) : d244746 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32536, d244746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32536, d244746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32200 q = 1) (hb : d241832 q = 1) : d244589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32200, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32200, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32537 q = 1) (hb : d241832 q = 1) : d244747 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32537, d244747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32537, d244747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32538 q = 1) (hb : d241832 q = 1) : d244748 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32538, d244748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32538, d244748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d32539 q = 1) (hb : d241832 q = 1) : d244749 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32539, d244749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32539, d244749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d32511 q = 1) (hb : d241832 q = 1) : d244745 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32511, d244745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32511, d244745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79217 q ha hb
  have h15 (q : Pattern) (ha : d32181 q = 1) (hb : d241832 q = 1) : d244588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32181, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79217 q ha hb
    | true =>
      simp only [d32181, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d32512 q = 1) (hb : d241832 q = 1) : d244746 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32512, d244746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d32512, d244746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d32182 q = 1) (hb : d241832 q = 1) : d244589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32182, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d32182, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d32513 q = 1) (hb : d241832 q = 1) : d244747 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32513, d244747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d32513, d244747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d32514 q = 1) (hb : d241832 q = 1) : d244748 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32514, d244748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d32514, d244748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d32525 q = 1) (hb : d241832 q = 1) : d244754 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32525, d244754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d32525, d244754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d32540 q = 1) (hb : d241832 q = 1) : d244755 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32540, d244755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32540, d244755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro79236 (p : Pattern) (ha : d32545 p = 1) (hb : d241832 p = 1) : d244760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32535 q = 1) (hb : d241832 q = 1) : d244745 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32535, d244745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32535, d244745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79220 q ha hb
  have h2 (q : Pattern) (ha : d32199 q = 1) (hb : d241832 q = 1) : d244588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32199, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79220 q ha hb
    | true =>
      simp only [d32199, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32536 q = 1) (hb : d241832 q = 1) : d244746 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32536, d244746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32536, d244746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32200 q = 1) (hb : d241832 q = 1) : d244589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32200, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32200, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32537 q = 1) (hb : d241832 q = 1) : d244747 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32537, d244747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32537, d244747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32538 q = 1) (hb : d241832 q = 1) : d244748 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32538, d244748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32538, d244748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32544 q = 1) (hb : d241832 q = 1) : d244754 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32544, d244754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32544, d244754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15412 q = 1) (hb : d241832 q = 1) : d1883 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d1883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d1883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79222 q ha hb
  have h9 (q : Pattern) (ha : d10135 q = 1) (hb : d241832 q = 1) : d1597 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d1597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79222 q ha hb
    | true =>
      simp only [d10135, d1597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15413 q = 1) (hb : d241832 q = 1) : d1884 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d1884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15413, d1884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10137 q = 1) (hb : d241832 q = 1) : d1598 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d1598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10137, d1598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15414 q = 1) (hb : d241832 q = 1) : d1885 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, d1885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15414, d1885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15415 q = 1) (hb : d241832 q = 1) : d1886 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, d1886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15415, d1886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15416 q = 1) (hb : d241832 q = 1) : d1887 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, d1887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15416, d1887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d32545 q = 1) (hb : d241832 q = 1) : d244760 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32545, d244760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32545, d244760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro79237 (p : Pattern) (ha : d32564 p = 1) (hb : d241832 p = 1) : d244779 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32546 q = 1) (hb : d241832 q = 1) : d244761 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32546, d244761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79235 q ha hb
    | true =>
      simp only [d32546, d244761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79236 q ha hb
  have h2 (q : Pattern) (ha : d32547 q = 1) (hb : d241832 q = 1) : d244762 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32547, d244762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32547, d244762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32548 q = 1) (hb : d241832 q = 1) : d244763 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32548, d244763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32548, d244763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32554 q = 1) (hb : d241832 q = 1) : d244769 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32554, d244769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32554, d244769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32563 q = 1) (hb : d241832 q = 1) : d244778 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32563, d244778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32563, d244778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32564 q = 1) (hb : d241832 q = 1) : d244779 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32564, d244779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32564, d244779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79238 (p : Pattern) (ha : d32664 p = 1) (hb : d241832 p = 1) : d244817 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32565 q = 1) (hb : d241832 q = 1) : d244780 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32565, d244780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79237 q ha hb
    | true =>
      simp only [d32565, d244780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32566 q = 1) (hb : d241832 q = 1) : d244781 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32566, d244781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32566, d244781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32661 q = 1) (hb : d241832 q = 1) : d244814 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32661, d244814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32661, d244814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32662 q = 1) (hb : d241832 q = 1) : d244815 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32662, d244815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32662, d244815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32663 q = 1) (hb : d241832 q = 1) : d244816 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32663, d244816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32663, d244816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32664 q = 1) (hb : d241832 q = 1) : d244817 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32664, d244817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32664, d244817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro79239 (p : Pattern) (ha : d32670 p = 1) (hb : d241832 p = 1) : d244823 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32665 q = 1) (hb : d241832 q = 1) : d244818 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d32665, d244818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79238 q ha hb
    | true =>
      simp only [d32665, d244818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32666 q = 1) (hb : d241832 q = 1) : d244819 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d32666, d244819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32666, d244819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32667 q = 1) (hb : d241832 q = 1) : d244820 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d32667, d244820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32667, d244820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32668 q = 1) (hb : d241832 q = 1) : d244821 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d32668, d244821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32668, d244821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32669 q = 1) (hb : d241832 q = 1) : d244822 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d32669, d244822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32669, d244822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32670 q = 1) (hb : d241832 q = 1) : d244823 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d32670, d244823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32670, d244823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79240 (p : Pattern) (ha : d32252 p = 1) (hb : d241832 p = 1) : d244641 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32218 q = 1) (hb : d241832 q = 1) : d244607 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32218, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79224 q ha hb
    | true =>
      simp only [d32218, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32219 q = 1) (hb : d241832 q = 1) : d244608 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32219, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32219, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32222 q = 1) (hb : d241832 q = 1) : d244611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79225 q ha hb
    | true =>
      simp only [d32222, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32223 q = 1) (hb : d241832 q = 1) : d244612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32224 q = 1) (hb : d241832 q = 1) : d244613 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32224, d244613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32224, d244613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32225 q = 1) (hb : d241832 q = 1) : d244614 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32225, d244614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32225, d244614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32251 q = 1) (hb : d241832 q = 1) : d244640 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32251, d244640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32251, d244640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32252 q = 1) (hb : d241832 q = 1) : d244641 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32252, d244641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32252, d244641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79241 (p : Pattern) (ha : d32254 p = 1) (hb : d241832 p = 1) : d244643 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32222 q = 1) (hb : d241832 q = 1) : d244611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79225 q ha hb
    | true =>
      simp only [d32222, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32223 q = 1) (hb : d241832 q = 1) : d244612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32228 q = 1) (hb : d241832 q = 1) : d244617 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32228, d244617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32228, d244617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32229 q = 1) (hb : d241832 q = 1) : d244618 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32229, d244618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32229, d244618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32253 q = 1) (hb : d241832 q = 1) : d244642 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32253, d244642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32253, d244642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32254 q = 1) (hb : d241832 q = 1) : d244643 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32254, d244643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32254, d244643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79242 (p : Pattern) (ha : d32261 p = 1) (hb : d241832 p = 1) : d244650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32218 q = 1) (hb : d241832 q = 1) : d244607 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32218, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79224 q ha hb
    | true =>
      simp only [d32218, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32219 q = 1) (hb : d241832 q = 1) : d244608 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32219, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32219, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32222 q = 1) (hb : d241832 q = 1) : d244611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79225 q ha hb
    | true =>
      simp only [d32222, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32223 q = 1) (hb : d241832 q = 1) : d244612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32224 q = 1) (hb : d241832 q = 1) : d244613 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32224, d244613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32224, d244613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32259 q = 1) (hb : d241832 q = 1) : d244648 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32259, d244648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32259, d244648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32260 q = 1) (hb : d241832 q = 1) : d244649 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32260, d244649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32260, d244649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32261 q = 1) (hb : d241832 q = 1) : d244650 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32261, d244650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32261, d244650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79243 (p : Pattern) (ha : d32264 p = 1) (hb : d241832 p = 1) : d244653 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32222 q = 1) (hb : d241832 q = 1) : d244611 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32222, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79225 q ha hb
    | true =>
      simp only [d32222, d244611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32223 q = 1) (hb : d241832 q = 1) : d244612 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32223, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32223, d244612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32228 q = 1) (hb : d241832 q = 1) : d244617 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32228, d244617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32228, d244617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32262 q = 1) (hb : d241832 q = 1) : d244651 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32262, d244651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32262, d244651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32263 q = 1) (hb : d241832 q = 1) : d244652 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32263, d244652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32263, d244652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32264 q = 1) (hb : d241832 q = 1) : d244653 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32264, d244653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32264, d244653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro79244 (p : Pattern) (ha : d32286 p = 1) (hb : d241832 p = 1) : d32171 p = 1 := by
  have h0 (q : Pattern) (ha : d31304 q = 1) (hb : d202304 q = 1) : d31304 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32140 q = 1) (hb : d202304 q = 1) : d32140 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d10054 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d32141 q = 1) (hb : d241830 q = 1) : d32166 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d32141, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32141, d241830, d32166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d241830 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d32142 q = 1) (hb : d241830 q = 1) : d32167 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32142, d32167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32143 q = 1) (hb : d241831 q = 1) : d32168 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d32143, d241831, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32143, d241831, d32168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d32284 q = 1) (hb : d241832 q = 1) : d32169 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32284, d241832, d32169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32284, d241832, d32169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d32285 q = 1) (hb : d241832 q = 1) : d32170 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32285, d32170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32285, d32170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32159 q = 1) (hb : d241832 q = 1) : d32159 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d32286 q = 1) (hb : d241832 q = 1) : d32171 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32286, d32171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32286, d32171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro79245 (p : Pattern) (ha : d32292 p = 1) (hb : d241832 p = 1) : d244595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32287 q = 1) (hb : d241832 q = 1) : d32172 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32287, d32172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79244 q ha hb
    | true =>
      simp only [d32287, d32172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32288 q = 1) (hb : d241832 q = 1) : d32173 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32288, d32173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32288, d32173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32289 q = 1) (hb : d241832 q = 1) : d32174 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32289, d32174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32289, d32174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32290 q = 1) (hb : d241832 q = 1) : d32175 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32290, d32175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32290, d32175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32181 q = 1) (hb : d241832 q = 1) : d244588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32181, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79217 q ha hb
    | true =>
      simp only [d32181, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32182 q = 1) (hb : d241832 q = 1) : d244589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32182, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32182, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32183 q = 1) (hb : d241832 q = 1) : d244590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32183, d244590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32183, d244590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32184 q = 1) (hb : d241832 q = 1) : d244591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32184, d244591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32184, d244591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32291 q = 1) (hb : d241832 q = 1) : d244592 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32291, d244592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32291, d244592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32204 q = 1) (hb : d241832 q = 1) : d244594 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32204, d244594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32204, d244594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32292 q = 1) (hb : d241832 q = 1) : d244595 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32292, d244595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32292, d244595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro79246 (p : Pattern) (ha : d32298 p = 1) (hb : d241832 p = 1) : d244662 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32280 q = 1) (hb : d241832 q = 1) : d32280 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32281 q = 1) (hb : d241832 q = 1) : d244657 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32281, d244657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32281, d244657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79218 q ha hb
  have h3 (q : Pattern) (ha : d32282 q = 1) (hb : d241832 q = 1) : d244658 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32282, d244658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32282, d244658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32283 q = 1) (hb : d241832 q = 1) : d244659 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32283, d244659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32283, d244659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32293 q = 1) (hb : d241832 q = 1) : d244596 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32293, d244596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79218 q ha hb
    | true =>
      simp only [d32293, d244596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79245 q ha hb
  have h6 (q : Pattern) (ha : d32294 q = 1) (hb : d241832 q = 1) : d244597 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32294, d244597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32294, d244597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d32295 q = 1) (hb : d241832 q = 1) : d244598 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32295, d244598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32295, d244598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32296 q = 1) (hb : d241832 q = 1) : d244660 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32296, d244660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32296, d244660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d32206 q = 1) (hb : d241832 q = 1) : d244596 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32206, d244596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79218 q ha hb
    | true =>
      simp only [d32206, d244596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79221 q ha hb
  have h10 (q : Pattern) (ha : d32207 q = 1) (hb : d241832 q = 1) : d244597 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32207, d244597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32207, d244597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d32208 q = 1) (hb : d241832 q = 1) : d244598 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32208, d244598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32208, d244598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d32211 q = 1) (hb : d241832 q = 1) : d244600 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d32211, d244600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79221 q ha hb
    | true =>
      simp only [d32211, d244600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79223 q ha hb
  have h13 (q : Pattern) (ha : d32212 q = 1) (hb : d241832 q = 1) : d244601 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32212, d244601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32212, d244601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d32213 q = 1) (hb : d241832 q = 1) : d244602 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d32213, d244602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32213, d244602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d32214 q = 1) (hb : d241832 q = 1) : d244603 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d32214, d244603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d32214, d244603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d32297 q = 1) (hb : d241832 q = 1) : d244661 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d32297, d244661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d32297, d244661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d32298 q = 1) (hb : d241832 q = 1) : d244662 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d32298, d244662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d32298, d244662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h17 p ha hb
theorem andIntro79247 (p : Pattern) (ha : d32304 p = 1) (hb : d241832 p = 1) : d244668 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32299 q = 1) (hb : d241832 q = 1) : d244663 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32299, d244663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79246 q ha hb
    | true =>
      simp only [d32299, d244663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32300 q = 1) (hb : d241832 q = 1) : d244664 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32300, d244664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32300, d244664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d32218 q = 1) (hb : d241832 q = 1) : d244607 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d32218, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79224 q ha hb
    | true =>
      simp only [d32218, d244607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d32219 q = 1) (hb : d241832 q = 1) : d244608 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d32219, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32219, d244608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d32301 q = 1) (hb : d241832 q = 1) : d244665 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d32301, d244665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32301, d244665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d32302 q = 1) (hb : d241832 q = 1) : d244666 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d32302, d244666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32302, d244666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32303 q = 1) (hb : d241832 q = 1) : d244667 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d32303, d244667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d32303, d244667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d32304 q = 1) (hb : d241832 q = 1) : d244668 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d32304, d244668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32304, d244668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro79248 (p : Pattern) (ha : d32404 p = 1) (hb : d241832 p = 1) : d244671 p = 1 := by
  have h0 (q : Pattern) (ha : d32157 q = 1) (hb : d241831 q = 1) : d32157 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d25767 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d32176 q = 1) (hb : d241832 q = 1) : d32158 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d32176, d241832, d32158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32176, d241832, d32158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d32177 q = 1) (hb : d241832 q = 1) : d32159 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d32177, d32159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d32177, d32159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5130 q = 1) (hb : d241831 q = 1) : d5130 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1578 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d5131 q = 1) (hb : d241832 q = 1) : d5627 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d5131, d241832, d5627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5131, d241832, d5627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d5132 q = 1) (hb : d241832 q = 1) : d5628 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d5132, d5628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d5132, d5628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d32404 q = 1) (hb : d241832 q = 1) : d244671 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d32404, d244671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32404, d244671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro79249 (p : Pattern) (ha : d32410 p = 1) (hb : d241832 p = 1) : d244677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d241832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d32194 q = 1) (hb : d241832 q = 1) : d32172 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32194, d32172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79219 q ha hb
    | true =>
      simp only [d32194, d32172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32195 q = 1) (hb : d241832 q = 1) : d32173 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32195, d32173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d32195, d32173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d32196 q = 1) (hb : d241832 q = 1) : d32174 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32196, d32174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32196, d32174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d32197 q = 1) (hb : d241832 q = 1) : d32175 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32197, d32175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d32197, d32175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32199 q = 1) (hb : d241832 q = 1) : d244588 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32199, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79220 q ha hb
    | true =>
      simp only [d32199, d244588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d32200 q = 1) (hb : d241832 q = 1) : d244589 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32200, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d32200, d244589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d32201 q = 1) (hb : d241832 q = 1) : d244590 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32201, d244590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32201, d244590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d32202 q = 1) (hb : d241832 q = 1) : d244591 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32202, d244591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d32202, d244591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32203 q = 1) (hb : d241832 q = 1) : d244592 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32203, d244592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d32203, d244592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d32405 q = 1) (hb : d241832 q = 1) : d244672 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d32405, d244672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro79248 q ha hb
    | true =>
      simp only [d32405, d244672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32406 q = 1) (hb : d241832 q = 1) : d244673 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d32406, d244673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d32406, d244673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d32407 q = 1) (hb : d241832 q = 1) : d244674 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d32407, d244674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32407, d244674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d32408 q = 1) (hb : d241832 q = 1) : d244675 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d32408, d244675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d32408, d244675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d32409 q = 1) (hb : d241832 q = 1) : d244676 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d32409, d244676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d32409, d244676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d32410 q = 1) (hb : d241832 q = 1) : d244677 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d32410, d244677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d32410, d244677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
end NetHack.Soko22Hazard87
