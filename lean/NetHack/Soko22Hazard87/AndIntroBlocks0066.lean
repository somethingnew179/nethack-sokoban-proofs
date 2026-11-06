import NetHack.Soko22Hazard87.AndIntroBlocks0065
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro16500 (p : Pattern) (ha : d7734 p = 1) (hb : d77844 p = 1) : d79993 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7730 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d77842 q = 1) : d1154 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7731 q = 1) (hb : d77844 q = 1) : d79990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7731, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7732 q = 1) (hb : d77844 q = 1) : d79991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7732, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7733 q = 1) (hb : d77844 q = 1) : d79992 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7733, d79992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7733, d79992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7734 q = 1) (hb : d77844 q = 1) : d79993 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7734, d79993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7734, d79993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16501 (p : Pattern) (ha : d7740 p = 1) (hb : d77845 p = 1) : d79999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1162 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7735 q = 1) (hb : d77845 q = 1) : d79994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d77845, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16500 q ha hb
    | true =>
      simp only [d7735, d77845, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7736 q = 1) (hb : d77845 q = 1) : d79995 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7737 q = 1) (hb : d77845 q = 1) : d79996 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7737, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7738 q = 1) (hb : d77845 q = 1) : d79997 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7739 q = 1) (hb : d77845 q = 1) : d79998 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7740 q = 1) (hb : d77845 q = 1) : d79999 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7740, d79999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7740, d79999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16502 (p : Pattern) (ha : d7743 p = 1) (hb : d77844 p = 1) : d80002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7730 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1154 q = 1) (hb : d77842 q = 1) : d1154 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7731 q = 1) (hb : d77844 q = 1) : d79990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7731, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7732 q = 1) (hb : d77844 q = 1) : d79991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7732, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7733 q = 1) (hb : d77844 q = 1) : d79992 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7733, d79992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7733, d79992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7743 q = 1) (hb : d77844 q = 1) : d80002 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7743, d80002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7743, d80002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16503 (p : Pattern) (ha : d7749 p = 1) (hb : d77845 p = 1) : d80008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1162 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7735 q = 1) (hb : d77845 q = 1) : d79994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d77845, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16500 q ha hb
    | true =>
      simp only [d7735, d77845, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7736 q = 1) (hb : d77845 q = 1) : d79995 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7737 q = 1) (hb : d77845 q = 1) : d79996 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7737, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7738 q = 1) (hb : d77845 q = 1) : d79997 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7739 q = 1) (hb : d77845 q = 1) : d79998 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1172 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7744 q = 1) (hb : d77845 q = 1) : d80003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7744, d77845, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16502 q ha hb
    | true =>
      simp only [d7744, d77845, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d7745 q = 1) (hb : d77845 q = 1) : d80004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, d80004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7745, d80004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7746 q = 1) (hb : d77845 q = 1) : d80005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, d80005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7746, d80005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7747 q = 1) (hb : d77845 q = 1) : d80006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, d80006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7747, d80006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d7748 q = 1) (hb : d77845 q = 1) : d80007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, d80007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7748, d80007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7749 q = 1) (hb : d77845 q = 1) : d80008 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7749, d80008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7749, d80008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16504 (p : Pattern) (ha : d7816 p = 1) (hb : d77845 p = 1) : d110127 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1162 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7735 q = 1) (hb : d77845 q = 1) : d79994 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d77845, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16500 q ha hb
    | true =>
      simp only [d7735, d77845, d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7736 q = 1) (hb : d77845 q = 1) : d79995 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7737 q = 1) (hb : d77845 q = 1) : d79996 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7737, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7738 q = 1) (hb : d77845 q = 1) : d79997 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7739 q = 1) (hb : d77845 q = 1) : d79998 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1350 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8233 q ha hb
    | true =>
      simp only [d1350, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1351 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1352 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1353 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1354 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7816 q = 1) (hb : d77845 q = 1) : d110127 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7816, d110127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7816, d110127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16505 (p : Pattern) (ha : d7754 p = 1) (hb : d77844 p = 1) : d80013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7730 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d77842 q = 1) : d1154 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7731 q = 1) (hb : d77844 q = 1) : d79990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7731, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7732 q = 1) (hb : d77844 q = 1) : d79991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7732, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7753 q = 1) (hb : d77844 q = 1) : d80012 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7753, d80012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7753, d80012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7754 q = 1) (hb : d77844 q = 1) : d80013 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7754, d80013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7754, d80013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16506 (p : Pattern) (ha : d7761 p = 1) (hb : d77844 p = 1) : d80020 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7730 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d77842 q = 1) : d1154 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7731 q = 1) (hb : d77844 q = 1) : d79990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7731, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7759 q = 1) (hb : d77844 q = 1) : d80018 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7759, d80018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7759, d80018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7760 q = 1) (hb : d77844 q = 1) : d80019 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7760, d80019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7760, d80019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7761 q = 1) (hb : d77844 q = 1) : d80020 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7761, d80020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7761, d80020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16507 (p : Pattern) (ha : d7772 p = 1) (hb : d77844 p = 1) : d80027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7768 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7730 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7769 q = 1) (hb : d77844 q = 1) : d80024 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7769, d77844, d80024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7769, d77844, d80024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7770 q = 1) (hb : d77844 q = 1) : d80025 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7770, d80025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7770, d80025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7771 q = 1) (hb : d77844 q = 1) : d80026 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7771, d80026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7771, d80026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7772 q = 1) (hb : d77844 q = 1) : d80027 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7772, d80027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7772, d80027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16508 (p : Pattern) (ha : d7787 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7730 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7784 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7784, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7784, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7785 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7786 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7787 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16509 (p : Pattern) (ha : d77845 p = 1) (hb : d85552 p = 1) : d110121 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1185 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7755 q = 1) (hb : d77845 q = 1) : d80014 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7755, d77845, d80014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16505 q ha hb
    | true =>
      simp only [d7755, d77845, d80014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7756 q = 1) (hb : d77845 q = 1) : d80015 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7756, d80015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7756, d80015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7757 q = 1) (hb : d77845 q = 1) : d80016 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7757, d80016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7757, d80016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7758 q = 1) (hb : d77845 q = 1) : d80017 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7758, d80017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7758, d80017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1195 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7762 q = 1) (hb : d77845 q = 1) : d80021 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7762, d77845, d80021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16506 q ha hb
    | true =>
      simp only [d7762, d77845, d80021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d7763 q = 1) (hb : d77845 q = 1) : d80022 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7763, d80022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7763, d80022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7764 q = 1) (hb : d77845 q = 1) : d80023 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7764, d80023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7764, d80023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7734 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7773 q = 1) (hb : d77845 q = 1) : d80028 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7773, d77845, d80028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16507 q ha hb
    | true =>
      simp only [d7773, d77845, d80028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d85548 q = 1) : d80029 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85548, d80029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85548, d80029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d7788 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7788, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16508 q ha hb
    | true =>
      simp only [d7788, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d7789 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d7789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85549 q = 1) : d110118 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85549, d110118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85549, d110118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d77845 q = 1) (hb : d85550 q = 1) : d110119 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85550, d110119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85550, d110119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77845 q = 1) (hb : d85551 q = 1) : d110120 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85551, d110120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85551, d110120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d77845 q = 1) (hb : d85552 q = 1) : d110121 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85552, d110121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85552, d110121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro16510 (p : Pattern) (ha : d7794 p = 1) (hb : d77844 p = 1) : d80035 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7730 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d77842 q = 1) : d1154 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7731 q = 1) (hb : d77844 q = 1) : d79990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7731, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7732 q = 1) (hb : d77844 q = 1) : d79991 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7732, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7753 q = 1) (hb : d77844 q = 1) : d80012 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7753, d80012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7753, d80012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7794 q = 1) (hb : d77844 q = 1) : d80035 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7794, d80035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7794, d80035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16511 (p : Pattern) (ha : d7799 p = 1) (hb : d77844 p = 1) : d80040 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7730 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d77842 q = 1) : d1154 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7731 q = 1) (hb : d77844 q = 1) : d79990 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7731, d77844, d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7759 q = 1) (hb : d77844 q = 1) : d80018 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7759, d80018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7759, d80018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7760 q = 1) (hb : d77844 q = 1) : d80019 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7760, d80019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7760, d80019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7799 q = 1) (hb : d77844 q = 1) : d80040 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7799, d80040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7799, d80040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16512 (p : Pattern) (ha : d7803 p = 1) (hb : d77844 p = 1) : d80044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7768 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7730 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7769 q = 1) (hb : d77844 q = 1) : d80024 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7769, d77844, d80024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7769, d77844, d80024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7770 q = 1) (hb : d77844 q = 1) : d80025 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7770, d80025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7770, d80025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7771 q = 1) (hb : d77844 q = 1) : d80026 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7771, d80026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7771, d80026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7803 q = 1) (hb : d77844 q = 1) : d80044 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7803, d80044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7803, d80044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16513 (p : Pattern) (ha : d7808 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7730 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7784 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7784, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7784, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7785 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7786 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7808 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16514 (p : Pattern) (ha : d77845 p = 1) (hb : d85557 p = 1) : d110125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1185 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7755 q = 1) (hb : d77845 q = 1) : d80014 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7755, d77845, d80014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16505 q ha hb
    | true =>
      simp only [d7755, d77845, d80014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7756 q = 1) (hb : d77845 q = 1) : d80015 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7756, d80015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7756, d80015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7757 q = 1) (hb : d77845 q = 1) : d80016 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7757, d80016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7757, d80016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7758 q = 1) (hb : d77845 q = 1) : d80017 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7758, d80017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7758, d80017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1195 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7762 q = 1) (hb : d77845 q = 1) : d80021 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7762, d77845, d80021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16506 q ha hb
    | true =>
      simp only [d7762, d77845, d80021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d7763 q = 1) (hb : d77845 q = 1) : d80022 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7763, d80022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7763, d80022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7764 q = 1) (hb : d77845 q = 1) : d80023 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7764, d80023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7764, d80023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7734 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7773 q = 1) (hb : d77845 q = 1) : d80028 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7773, d77845, d80028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16507 q ha hb
    | true =>
      simp only [d7773, d77845, d80028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d85548 q = 1) : d80029 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85548, d80029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85548, d80029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d7788 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7788, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16508 q ha hb
    | true =>
      simp only [d7788, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d7789 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d7789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85549 q = 1) : d110118 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85549, d110118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85549, d110118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d77845 q = 1) (hb : d85550 q = 1) : d110119 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85550, d110119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85550, d110119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77845 q = 1) (hb : d85551 q = 1) : d110120 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85551, d110120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85551, d110120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d1327 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d7795 q = 1) (hb : d77845 q = 1) : d80036 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7795, d77845, d80036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16510 q ha hb
    | true =>
      simp only [d7795, d77845, d80036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d7796 q = 1) (hb : d77845 q = 1) : d80037 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7796, d80037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7796, d80037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d7797 q = 1) (hb : d77845 q = 1) : d80038 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7797, d80038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d7797, d80038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d7798 q = 1) (hb : d77845 q = 1) : d80039 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7798, d80039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7798, d80039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d1333 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d7800 q = 1) (hb : d77845 q = 1) : d80041 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7800, d77845, d80041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16511 q ha hb
    | true =>
      simp only [d7800, d77845, d80041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d7801 q = 1) (hb : d77845 q = 1) : d80042 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7801, d80042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7801, d80042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d7802 q = 1) (hb : d77845 q = 1) : d80043 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7802, d80043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d7802, d80043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d7743 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d7804 q = 1) (hb : d77845 q = 1) : d80045 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7804, d77845, d80045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16512 q ha hb
    | true =>
      simp only [d7804, d77845, d80045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d77845 q = 1) (hb : d85553 q = 1) : d80046 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85553, d80046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
    | true =>
      simp only [d85553, d80046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d7809 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7809, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16513 q ha hb
    | true =>
      simp only [d7809, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h32 (q : Pattern) (ha : d7810 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
    | true =>
      simp only [d7810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h33 (q : Pattern) (ha : d77845 q = 1) (hb : d85554 q = 1) : d110122 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85554, d110122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d85554, d110122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q hb ha
  have h34 (q : Pattern) (ha : d77845 q = 1) (hb : d85555 q = 1) : d110123 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85555, d110123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
    | true =>
      simp only [d85555, d110123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d77845 q = 1) (hb : d85556 q = 1) : d110124 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85556, d110124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d85556, d110124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  have h36 (q : Pattern) (ha : d77845 q = 1) (hb : d85557 q = 1) : d110125 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85557, d110125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85557, d110125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h35 q ha hb
  exact h36 p ha hb
theorem andIntro16515 (p : Pattern) (ha : d77845 p = 1) (hb : d85564 p = 1) : d110134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7743 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7804 q = 1) (hb : d77845 q = 1) : d80045 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7804, d77845, d80045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16512 q ha hb
    | true =>
      simp only [d7804, d77845, d80045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85553 q = 1) : d80046 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85553, d80046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85553, d80046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7809 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7809, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16513 q ha hb
    | true =>
      simp only [d7809, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7810 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d85554 q = 1) : d110122 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85554, d110122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85554, d110122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85562 q = 1) : d110132 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85562, d110132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85562, d110132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85563 q = 1) : d110133 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85563, d110133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85563, d110133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85564 q = 1) : d110134 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85564, d110134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85564, d110134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16516 (p : Pattern) (ha : d7840 p = 1) (hb : d77844 p = 1) : d80067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7832 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7836 q = 1) (hb : d77842 q = 1) : d7836 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7837 q = 1) (hb : d77844 q = 1) : d80064 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7837, d77844, d80064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7837, d77844, d80064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7838 q = 1) (hb : d77844 q = 1) : d80065 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7838, d80065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7838, d80065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7839 q = 1) (hb : d77844 q = 1) : d80066 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7839, d80066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7839, d80066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7840 q = 1) (hb : d77844 q = 1) : d80067 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7840, d80067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7840, d80067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16517 (p : Pattern) (ha : d7859 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7856 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7856, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7856, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7857 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7858 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7859 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16518 (p : Pattern) (ha : d77845 p = 1) (hb : d85574 p = 1) : d110143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7844 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7845 q = 1) (hb : d77845 q = 1) : d80068 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7845, d77845, d80068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16516 q ha hb
    | true =>
      simp only [d7845, d77845, d80068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85570 q = 1) : d80069 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85570, d80069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85570, d80069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7860 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7860, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16517 q ha hb
    | true =>
      simp only [d7860, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7861 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d85571 q = 1) : d110140 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85571, d110140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85571, d110140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85572 q = 1) : d110141 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85572, d110141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85572, d110141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85573 q = 1) : d110142 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85573, d110142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85573, d110142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85574 q = 1) : d110143 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85574, d110143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85574, d110143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16519 (p : Pattern) (ha : d77845 p = 1) (hb : d85580 p = 1) : d110149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7741 q = 1) (hb : d77845 q = 1) : d80000 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7741, d80000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7741, d80000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16501 q ha hb
  have h2 (q : Pattern) (ha : d7742 q = 1) (hb : d77845 q = 1) : d80001 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7742, d80001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7742, d80001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7750 q = 1) (hb : d77845 q = 1) : d80009 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7750, d80009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16501 q ha hb
    | true =>
      simp only [d7750, d80009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16503 q ha hb
  have h4 (q : Pattern) (ha : d7751 q = 1) (hb : d77845 q = 1) : d80010 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7751, d80010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7751, d80010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7752 q = 1) (hb : d77845 q = 1) : d80011 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7752, d80011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7752, d80011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85558 q = 1) : d110126 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85558, d110126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16509 q ha hb
    | true =>
      simp only [d85558, d110126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16514 q ha hb
  have h7 (q : Pattern) (ha : d7817 q = 1) (hb : d77845 q = 1) : d110128 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7817, d110128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16504 q ha hb
    | true =>
      simp only [d7817, d110128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8235 q ha hb
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85559 q = 1) : d110129 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85559, d110129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85559, d110129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85560 q = 1) : d110130 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85560, d110130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85560, d110130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85561 q = 1) : d110131 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85561, d110131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85561, d110131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77845 q = 1) (hb : d85565 q = 1) : d110135 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85565, d110135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85565, d110135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16515 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8236 q ha hb
  have h13 (q : Pattern) (ha : d77845 q = 1) (hb : d85566 q = 1) : d110136 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85566, d110136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85566, d110136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d77845 q = 1) (hb : d85567 q = 1) : d110137 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85567, d110137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85567, d110137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d77845 q = 1) (hb : d85568 q = 1) : d110138 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85568, d110138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85568, d110138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85569 q = 1) : d110139 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85569, d110139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85569, d110139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77845 q = 1) (hb : d85575 q = 1) : d110144 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85575, d110144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85575, d110144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16518 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8238 q ha hb
  have h19 (q : Pattern) (ha : d77845 q = 1) (hb : d85576 q = 1) : d110145 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85576, d110145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85576, d110145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d77845 q = 1) (hb : d85577 q = 1) : d110146 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85577, d110146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d85577, d110146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d77845 q = 1) (hb : d85578 q = 1) : d110147 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85578, d110147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85578, d110147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d77845 q = 1) (hb : d85579 q = 1) : d110148 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85579, d110148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85579, d110148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d77845 q = 1) (hb : d85580 q = 1) : d110149 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85580, d110149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85580, d110149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro16520 (p : Pattern) (ha : d77845 p = 1) (hb : d85586 p = 1) : d110155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d85581 q = 1) : d110150 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85581, d110150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85581, d110150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16519 q ha hb
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d85582 q = 1) : d110151 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85582, d110151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85582, d110151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85583 q = 1) : d110152 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85583, d110152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85583, d110152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d85584 q = 1) : d110153 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85584, d110153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85584, d110153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d85585 q = 1) : d110154 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85585, d110154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85585, d110154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85586 q = 1) : d110155 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85586, d110155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85586, d110155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16521 (p : Pattern) (ha : d7888 p = 1) (hb : d77844 p = 1) : d80098 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7884 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d77842 q = 1) : d1615 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7885 q = 1) (hb : d77844 q = 1) : d80095 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7885, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7886 q = 1) (hb : d77844 q = 1) : d80096 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7886, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7887 q = 1) (hb : d77844 q = 1) : d80097 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7887, d80097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7887, d80097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7888 q = 1) (hb : d77844 q = 1) : d80098 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7888, d80098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7888, d80098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16522 (p : Pattern) (ha : d7894 p = 1) (hb : d77845 p = 1) : d80104 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1623 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7889 q = 1) (hb : d77845 q = 1) : d80099 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d77845, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16521 q ha hb
    | true =>
      simp only [d7889, d77845, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7890 q = 1) (hb : d77845 q = 1) : d80100 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7891 q = 1) (hb : d77845 q = 1) : d80101 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7891, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7892 q = 1) (hb : d77845 q = 1) : d80102 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7893 q = 1) (hb : d77845 q = 1) : d80103 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7894 q = 1) (hb : d77845 q = 1) : d80104 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7894, d80104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7894, d80104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16523 (p : Pattern) (ha : d7897 p = 1) (hb : d77844 p = 1) : d80107 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7884 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1615 q = 1) (hb : d77842 q = 1) : d1615 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7885 q = 1) (hb : d77844 q = 1) : d80095 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7885, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7886 q = 1) (hb : d77844 q = 1) : d80096 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7886, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7887 q = 1) (hb : d77844 q = 1) : d80097 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7887, d80097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7887, d80097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7897 q = 1) (hb : d77844 q = 1) : d80107 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7897, d80107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7897, d80107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16524 (p : Pattern) (ha : d7903 p = 1) (hb : d77845 p = 1) : d80113 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1623 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7889 q = 1) (hb : d77845 q = 1) : d80099 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d77845, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16521 q ha hb
    | true =>
      simp only [d7889, d77845, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7890 q = 1) (hb : d77845 q = 1) : d80100 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7891 q = 1) (hb : d77845 q = 1) : d80101 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7891, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7892 q = 1) (hb : d77845 q = 1) : d80102 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7893 q = 1) (hb : d77845 q = 1) : d80103 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1633 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7898 q = 1) (hb : d77845 q = 1) : d80108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7898, d77845, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16523 q ha hb
    | true =>
      simp only [d7898, d77845, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d7899 q = 1) (hb : d77845 q = 1) : d80109 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, d80109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7899, d80109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7900 q = 1) (hb : d77845 q = 1) : d80110 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, d80110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7900, d80110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7901 q = 1) (hb : d77845 q = 1) : d80111 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, d80111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7901, d80111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d7902 q = 1) (hb : d77845 q = 1) : d80112 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, d80112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7902, d80112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7903 q = 1) (hb : d77845 q = 1) : d80113 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7903, d80113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7903, d80113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16525 (p : Pattern) (ha : d7970 p = 1) (hb : d77845 p = 1) : d110168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1623 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7889 q = 1) (hb : d77845 q = 1) : d80099 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d77845, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16521 q ha hb
    | true =>
      simp only [d7889, d77845, d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7890 q = 1) (hb : d77845 q = 1) : d80100 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7891 q = 1) (hb : d77845 q = 1) : d80101 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7891, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7892 q = 1) (hb : d77845 q = 1) : d80102 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7893 q = 1) (hb : d77845 q = 1) : d80103 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1827 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8261 q ha hb
    | true =>
      simp only [d1827, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d1828 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1829 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d1830 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1831 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7970 q = 1) (hb : d77845 q = 1) : d110168 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7970, d110168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7970, d110168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16526 (p : Pattern) (ha : d7908 p = 1) (hb : d77844 p = 1) : d80118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7884 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d77842 q = 1) : d1615 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7885 q = 1) (hb : d77844 q = 1) : d80095 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7885, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7886 q = 1) (hb : d77844 q = 1) : d80096 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7886, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7907 q = 1) (hb : d77844 q = 1) : d80117 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7907, d80117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7907, d80117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7908 q = 1) (hb : d77844 q = 1) : d80118 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7908, d80118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7908, d80118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16527 (p : Pattern) (ha : d7915 p = 1) (hb : d77844 p = 1) : d80125 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7884 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d77842 q = 1) : d1615 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7885 q = 1) (hb : d77844 q = 1) : d80095 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7885, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7913 q = 1) (hb : d77844 q = 1) : d80123 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7913, d80123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7913, d80123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7914 q = 1) (hb : d77844 q = 1) : d80124 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7914, d80124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7914, d80124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7915 q = 1) (hb : d77844 q = 1) : d80125 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7915, d80125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7915, d80125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16528 (p : Pattern) (ha : d7926 p = 1) (hb : d77844 p = 1) : d80132 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7922 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7884 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7923 q = 1) (hb : d77844 q = 1) : d80129 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7923, d77844, d80129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7923, d77844, d80129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7924 q = 1) (hb : d77844 q = 1) : d80130 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7924, d80130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7924, d80130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7925 q = 1) (hb : d77844 q = 1) : d80131 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7925, d80131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7925, d80131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7926 q = 1) (hb : d77844 q = 1) : d80132 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7926, d80132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7926, d80132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16529 (p : Pattern) (ha : d7941 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7884 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7938 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7938, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7938, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7939 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7940 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7941 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16530 (p : Pattern) (ha : d77845 p = 1) (hb : d85594 p = 1) : d110162 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1646 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7909 q = 1) (hb : d77845 q = 1) : d80119 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7909, d77845, d80119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16526 q ha hb
    | true =>
      simp only [d7909, d77845, d80119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7910 q = 1) (hb : d77845 q = 1) : d80120 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7910, d80120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7910, d80120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7911 q = 1) (hb : d77845 q = 1) : d80121 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7911, d80121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7911, d80121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7912 q = 1) (hb : d77845 q = 1) : d80122 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7912, d80122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7912, d80122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1656 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7916 q = 1) (hb : d77845 q = 1) : d80126 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7916, d77845, d80126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16527 q ha hb
    | true =>
      simp only [d7916, d77845, d80126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d7917 q = 1) (hb : d77845 q = 1) : d80127 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7917, d80127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7917, d80127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7918 q = 1) (hb : d77845 q = 1) : d80128 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7918, d80128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7918, d80128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7888 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7927 q = 1) (hb : d77845 q = 1) : d80133 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7927, d77845, d80133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16528 q ha hb
    | true =>
      simp only [d7927, d77845, d80133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d85590 q = 1) : d80134 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85590, d80134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85590, d80134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d7942 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7942, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16529 q ha hb
    | true =>
      simp only [d7942, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d7943 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d7943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85591 q = 1) : d110159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85591, d110159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85591, d110159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d77845 q = 1) (hb : d85592 q = 1) : d110160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85592, d110160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85592, d110160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77845 q = 1) (hb : d85593 q = 1) : d110161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85593, d110161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85593, d110161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d77845 q = 1) (hb : d85594 q = 1) : d110162 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85594, d110162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85594, d110162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro16531 (p : Pattern) (ha : d7948 p = 1) (hb : d77844 p = 1) : d80140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7884 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d77842 q = 1) : d1615 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7885 q = 1) (hb : d77844 q = 1) : d80095 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7885, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7886 q = 1) (hb : d77844 q = 1) : d80096 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7886, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7907 q = 1) (hb : d77844 q = 1) : d80117 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7907, d80117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7907, d80117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7948 q = 1) (hb : d77844 q = 1) : d80140 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7948, d80140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7948, d80140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16532 (p : Pattern) (ha : d7953 p = 1) (hb : d77844 p = 1) : d80145 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7884 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d77842 q = 1) : d1615 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7885 q = 1) (hb : d77844 q = 1) : d80095 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7885, d77844, d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7913 q = 1) (hb : d77844 q = 1) : d80123 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7913, d80123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7913, d80123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7914 q = 1) (hb : d77844 q = 1) : d80124 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7914, d80124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7914, d80124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7953 q = 1) (hb : d77844 q = 1) : d80145 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7953, d80145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7953, d80145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16533 (p : Pattern) (ha : d7957 p = 1) (hb : d77844 p = 1) : d80149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7922 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7884 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7923 q = 1) (hb : d77844 q = 1) : d80129 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7923, d77844, d80129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7923, d77844, d80129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7924 q = 1) (hb : d77844 q = 1) : d80130 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7924, d80130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7924, d80130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7925 q = 1) (hb : d77844 q = 1) : d80131 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7925, d80131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7925, d80131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7957 q = 1) (hb : d77844 q = 1) : d80149 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7957, d80149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7957, d80149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16534 (p : Pattern) (ha : d7962 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7884 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7938 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7938, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7938, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7939 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7940 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7962 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16535 (p : Pattern) (ha : d77845 p = 1) (hb : d85599 p = 1) : d110166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1646 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7909 q = 1) (hb : d77845 q = 1) : d80119 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7909, d77845, d80119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16526 q ha hb
    | true =>
      simp only [d7909, d77845, d80119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7910 q = 1) (hb : d77845 q = 1) : d80120 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7910, d80120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7910, d80120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7911 q = 1) (hb : d77845 q = 1) : d80121 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7911, d80121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7911, d80121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7912 q = 1) (hb : d77845 q = 1) : d80122 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7912, d80122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7912, d80122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1656 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7916 q = 1) (hb : d77845 q = 1) : d80126 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7916, d77845, d80126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16527 q ha hb
    | true =>
      simp only [d7916, d77845, d80126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d7917 q = 1) (hb : d77845 q = 1) : d80127 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7917, d80127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7917, d80127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7918 q = 1) (hb : d77845 q = 1) : d80128 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7918, d80128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7918, d80128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7888 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7927 q = 1) (hb : d77845 q = 1) : d80133 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7927, d77845, d80133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16528 q ha hb
    | true =>
      simp only [d7927, d77845, d80133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d85590 q = 1) : d80134 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85590, d80134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85590, d80134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d7942 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7942, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16529 q ha hb
    | true =>
      simp only [d7942, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d7943 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d7943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85591 q = 1) : d110159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85591, d110159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85591, d110159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d77845 q = 1) (hb : d85592 q = 1) : d110160 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85592, d110160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85592, d110160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77845 q = 1) (hb : d85593 q = 1) : d110161 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85593, d110161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85593, d110161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d1804 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d7949 q = 1) (hb : d77845 q = 1) : d80141 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7949, d77845, d80141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16531 q ha hb
    | true =>
      simp only [d7949, d77845, d80141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d7950 q = 1) (hb : d77845 q = 1) : d80142 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7950, d80142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7950, d80142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d7951 q = 1) (hb : d77845 q = 1) : d80143 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7951, d80143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d7951, d80143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d7952 q = 1) (hb : d77845 q = 1) : d80144 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7952, d80144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7952, d80144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d1810 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d7954 q = 1) (hb : d77845 q = 1) : d80146 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7954, d77845, d80146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16532 q ha hb
    | true =>
      simp only [d7954, d77845, d80146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d7955 q = 1) (hb : d77845 q = 1) : d80147 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7955, d80147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7955, d80147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d7956 q = 1) (hb : d77845 q = 1) : d80148 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7956, d80148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d7956, d80148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d7897 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d7958 q = 1) (hb : d77845 q = 1) : d80150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7958, d77845, d80150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16533 q ha hb
    | true =>
      simp only [d7958, d77845, d80150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d77845 q = 1) (hb : d85595 q = 1) : d80151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85595, d80151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
    | true =>
      simp only [d85595, d80151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d7963 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7963, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16534 q ha hb
    | true =>
      simp only [d7963, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h32 (q : Pattern) (ha : d7964 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
    | true =>
      simp only [d7964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h33 (q : Pattern) (ha : d77845 q = 1) (hb : d85596 q = 1) : d110163 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85596, d110163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d85596, d110163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q hb ha
  have h34 (q : Pattern) (ha : d77845 q = 1) (hb : d85597 q = 1) : d110164 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85597, d110164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
    | true =>
      simp only [d85597, d110164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d77845 q = 1) (hb : d85598 q = 1) : d110165 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85598, d110165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d85598, d110165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  have h36 (q : Pattern) (ha : d77845 q = 1) (hb : d85599 q = 1) : d110166 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85599, d110166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85599, d110166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h35 q ha hb
  exact h36 p ha hb
theorem andIntro16536 (p : Pattern) (ha : d77845 p = 1) (hb : d85606 p = 1) : d110175 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7897 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7958 q = 1) (hb : d77845 q = 1) : d80150 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7958, d77845, d80150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16533 q ha hb
    | true =>
      simp only [d7958, d77845, d80150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85595 q = 1) : d80151 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85595, d80151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85595, d80151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7963 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7963, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16534 q ha hb
    | true =>
      simp only [d7963, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7964 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d85596 q = 1) : d110163 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85596, d110163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85596, d110163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85604 q = 1) : d110173 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85604, d110173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85604, d110173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85605 q = 1) : d110174 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85605, d110174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85605, d110174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85606 q = 1) : d110175 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85606, d110175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85606, d110175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16537 (p : Pattern) (ha : d7994 p = 1) (hb : d77844 p = 1) : d80172 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7986 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7990 q = 1) (hb : d77842 q = 1) : d7990 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7991 q = 1) (hb : d77844 q = 1) : d80169 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7991, d77844, d80169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7991, d77844, d80169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7992 q = 1) (hb : d77844 q = 1) : d80170 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7992, d80170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7992, d80170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7993 q = 1) (hb : d77844 q = 1) : d80171 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7993, d80171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7993, d80171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7994 q = 1) (hb : d77844 q = 1) : d80172 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7994, d80172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7994, d80172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16538 (p : Pattern) (ha : d8013 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7990 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8010 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8010, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d8010, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8011 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8012 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8013 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16539 (p : Pattern) (ha : d77845 p = 1) (hb : d85616 p = 1) : d110184 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7998 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7999 q = 1) (hb : d77845 q = 1) : d80173 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7999, d77845, d80173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16537 q ha hb
    | true =>
      simp only [d7999, d77845, d80173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85612 q = 1) : d80174 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85612, d80174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85612, d80174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8014 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8014, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16538 q ha hb
    | true =>
      simp only [d8014, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8015 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d85613 q = 1) : d110181 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85613, d110181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85613, d110181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85614 q = 1) : d110182 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85614, d110182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85614, d110182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85615 q = 1) : d110183 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85615, d110183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85615, d110183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85616 q = 1) : d110184 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85616, d110184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85616, d110184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16540 (p : Pattern) (ha : d77845 p = 1) (hb : d85622 p = 1) : d110190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7895 q = 1) (hb : d77845 q = 1) : d80105 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7895, d80105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7895, d80105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16522 q ha hb
  have h2 (q : Pattern) (ha : d7896 q = 1) (hb : d77845 q = 1) : d80106 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7896, d80106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7896, d80106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7904 q = 1) (hb : d77845 q = 1) : d80114 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7904, d80114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16522 q ha hb
    | true =>
      simp only [d7904, d80114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16524 q ha hb
  have h4 (q : Pattern) (ha : d7905 q = 1) (hb : d77845 q = 1) : d80115 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7905, d80115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7905, d80115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7906 q = 1) (hb : d77845 q = 1) : d80116 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7906, d80116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7906, d80116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85600 q = 1) : d110167 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85600, d110167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16530 q ha hb
    | true =>
      simp only [d85600, d110167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16535 q ha hb
  have h7 (q : Pattern) (ha : d7971 q = 1) (hb : d77845 q = 1) : d110169 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7971, d110169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16525 q ha hb
    | true =>
      simp only [d7971, d110169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8263 q ha hb
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85601 q = 1) : d110170 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85601, d110170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85601, d110170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85602 q = 1) : d110171 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85602, d110171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85602, d110171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85603 q = 1) : d110172 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85603, d110172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85603, d110172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77845 q = 1) (hb : d85607 q = 1) : d110176 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85607, d110176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85607, d110176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16536 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8264 q ha hb
  have h13 (q : Pattern) (ha : d77845 q = 1) (hb : d85608 q = 1) : d110177 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85608, d110177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85608, d110177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d77845 q = 1) (hb : d85609 q = 1) : d110178 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85609, d110178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85609, d110178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d77845 q = 1) (hb : d85610 q = 1) : d110179 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85610, d110179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85610, d110179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85611 q = 1) : d110180 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85611, d110180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85611, d110180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77845 q = 1) (hb : d85617 q = 1) : d110185 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85617, d110185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85617, d110185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16539 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8266 q ha hb
  have h19 (q : Pattern) (ha : d77845 q = 1) (hb : d85618 q = 1) : d110186 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85618, d110186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85618, d110186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d77845 q = 1) (hb : d85619 q = 1) : d110187 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85619, d110187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d85619, d110187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d77845 q = 1) (hb : d85620 q = 1) : d110188 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85620, d110188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85620, d110188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d77845 q = 1) (hb : d85621 q = 1) : d110189 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85621, d110189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85621, d110189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d77845 q = 1) (hb : d85622 q = 1) : d110190 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85622, d110190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85622, d110190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro16541 (p : Pattern) (ha : d77845 p = 1) (hb : d85628 p = 1) : d110196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d85623 q = 1) : d110191 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85623, d110191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85623, d110191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16540 q ha hb
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d85624 q = 1) : d110192 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85624, d110192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85624, d110192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85625 q = 1) : d110193 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85625, d110193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85625, d110193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d85626 q = 1) : d110194 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85626, d110194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85626, d110194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d85627 q = 1) : d110195 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85627, d110195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85627, d110195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85628 q = 1) : d110196 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85628, d110196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85628, d110196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16542 (p : Pattern) (ha : d8043 p = 1) (hb : d77844 p = 1) : d80204 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8039 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d77842 q = 1) : d2098 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8040 q = 1) (hb : d77844 q = 1) : d80201 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d8040, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8041 q = 1) (hb : d77844 q = 1) : d80202 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8041, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8042 q = 1) (hb : d77844 q = 1) : d80203 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8042, d80203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8042, d80203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8043 q = 1) (hb : d77844 q = 1) : d80204 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8043, d80204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8043, d80204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16543 (p : Pattern) (ha : d8049 p = 1) (hb : d77845 p = 1) : d80210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2106 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8044 q = 1) (hb : d77845 q = 1) : d80205 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d77845, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16542 q ha hb
    | true =>
      simp only [d8044, d77845, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d8045 q = 1) (hb : d77845 q = 1) : d80206 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8046 q = 1) (hb : d77845 q = 1) : d80207 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8046, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8047 q = 1) (hb : d77845 q = 1) : d80208 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8048 q = 1) (hb : d77845 q = 1) : d80209 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8049 q = 1) (hb : d77845 q = 1) : d80210 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8049, d80210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8049, d80210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16544 (p : Pattern) (ha : d8052 p = 1) (hb : d77844 p = 1) : d80213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8039 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2098 q = 1) (hb : d77842 q = 1) : d2098 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8040 q = 1) (hb : d77844 q = 1) : d80201 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d8040, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8041 q = 1) (hb : d77844 q = 1) : d80202 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8041, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8042 q = 1) (hb : d77844 q = 1) : d80203 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8042, d80203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8042, d80203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8052 q = 1) (hb : d77844 q = 1) : d80213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8052, d80213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8052, d80213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16545 (p : Pattern) (ha : d8058 p = 1) (hb : d77845 p = 1) : d80219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2106 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8044 q = 1) (hb : d77845 q = 1) : d80205 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d77845, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16542 q ha hb
    | true =>
      simp only [d8044, d77845, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d8045 q = 1) (hb : d77845 q = 1) : d80206 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8046 q = 1) (hb : d77845 q = 1) : d80207 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8046, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8047 q = 1) (hb : d77845 q = 1) : d80208 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8048 q = 1) (hb : d77845 q = 1) : d80209 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2116 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8053 q = 1) (hb : d77845 q = 1) : d80214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8053, d77845, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16544 q ha hb
    | true =>
      simp only [d8053, d77845, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d8054 q = 1) (hb : d77845 q = 1) : d80215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, d80215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8054, d80215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8055 q = 1) (hb : d77845 q = 1) : d80216 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, d80216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8055, d80216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8056 q = 1) (hb : d77845 q = 1) : d80217 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, d80217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8056, d80217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d8057 q = 1) (hb : d77845 q = 1) : d80218 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, d80218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8057, d80218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d8058 q = 1) (hb : d77845 q = 1) : d80219 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8058, d80219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8058, d80219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16546 (p : Pattern) (ha : d8125 p = 1) (hb : d77845 p = 1) : d110210 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2106 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8044 q = 1) (hb : d77845 q = 1) : d80205 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d77845, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16542 q ha hb
    | true =>
      simp only [d8044, d77845, d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d8045 q = 1) (hb : d77845 q = 1) : d80206 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8046 q = 1) (hb : d77845 q = 1) : d80207 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8046, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8047 q = 1) (hb : d77845 q = 1) : d80208 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8048 q = 1) (hb : d77845 q = 1) : d80209 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2305 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8289 q ha hb
    | true =>
      simp only [d2305, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d2306 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2307 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d2308 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2309 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d8125 q = 1) (hb : d77845 q = 1) : d110210 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8125, d110210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8125, d110210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16547 (p : Pattern) (ha : d8063 p = 1) (hb : d77844 p = 1) : d80224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8039 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d77842 q = 1) : d2098 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8040 q = 1) (hb : d77844 q = 1) : d80201 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d8040, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8041 q = 1) (hb : d77844 q = 1) : d80202 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8041, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8062 q = 1) (hb : d77844 q = 1) : d80223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8062, d80223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8062, d80223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8063 q = 1) (hb : d77844 q = 1) : d80224 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8063, d80224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8063, d80224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16548 (p : Pattern) (ha : d8070 p = 1) (hb : d77844 p = 1) : d80231 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8039 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d77842 q = 1) : d2098 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8040 q = 1) (hb : d77844 q = 1) : d80201 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d8040, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8068 q = 1) (hb : d77844 q = 1) : d80229 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8068, d80229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8068, d80229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8069 q = 1) (hb : d77844 q = 1) : d80230 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8069, d80230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8069, d80230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8070 q = 1) (hb : d77844 q = 1) : d80231 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8070, d80231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8070, d80231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16549 (p : Pattern) (ha : d8081 p = 1) (hb : d77844 p = 1) : d80238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8077 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8039 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8078 q = 1) (hb : d77844 q = 1) : d80235 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8078, d77844, d80235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d8078, d77844, d80235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8079 q = 1) (hb : d77844 q = 1) : d80236 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8079, d80236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8079, d80236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8080 q = 1) (hb : d77844 q = 1) : d80237 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8080, d80237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8080, d80237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8081 q = 1) (hb : d77844 q = 1) : d80238 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8081, d80238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8081, d80238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16550 (p : Pattern) (ha : d8096 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8039 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8093 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8093, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d8093, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8094 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8095 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8096 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16551 (p : Pattern) (ha : d77845 p = 1) (hb : d85637 p = 1) : d110204 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8064 q = 1) (hb : d77845 q = 1) : d80225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8064, d77845, d80225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16547 q ha hb
    | true =>
      simp only [d8064, d77845, d80225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d8065 q = 1) (hb : d77845 q = 1) : d80226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8065, d80226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8065, d80226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8066 q = 1) (hb : d77845 q = 1) : d80227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8066, d80227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8066, d80227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8067 q = 1) (hb : d77845 q = 1) : d80228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8067, d80228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8067, d80228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d2139 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8071 q = 1) (hb : d77845 q = 1) : d80232 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8071, d77845, d80232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16548 q ha hb
    | true =>
      simp only [d8071, d77845, d80232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d8072 q = 1) (hb : d77845 q = 1) : d80233 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8072, d80233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8072, d80233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8073 q = 1) (hb : d77845 q = 1) : d80234 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8073, d80234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8073, d80234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8043 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d8082 q = 1) (hb : d77845 q = 1) : d80239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8082, d77845, d80239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16549 q ha hb
    | true =>
      simp only [d8082, d77845, d80239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d85633 q = 1) : d80240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85633, d80240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85633, d80240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d8097 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8097, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16550 q ha hb
    | true =>
      simp only [d8097, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8098 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d8098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85634 q = 1) : d110201 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85634, d110201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85634, d110201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d77845 q = 1) (hb : d85635 q = 1) : d110202 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85635, d110202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85635, d110202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77845 q = 1) (hb : d85636 q = 1) : d110203 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85636, d110203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85636, d110203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d77845 q = 1) (hb : d85637 q = 1) : d110204 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85637, d110204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85637, d110204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro16552 (p : Pattern) (ha : d8103 p = 1) (hb : d77844 p = 1) : d80246 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8039 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d77842 q = 1) : d2098 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8040 q = 1) (hb : d77844 q = 1) : d80201 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d8040, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8041 q = 1) (hb : d77844 q = 1) : d80202 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8041, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8062 q = 1) (hb : d77844 q = 1) : d80223 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8062, d80223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8062, d80223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8103 q = 1) (hb : d77844 q = 1) : d80246 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8103, d80246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8103, d80246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16553 (p : Pattern) (ha : d8108 p = 1) (hb : d77844 p = 1) : d80251 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8039 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d77842 q = 1) : d2098 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8040 q = 1) (hb : d77844 q = 1) : d80201 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d8040, d77844, d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8068 q = 1) (hb : d77844 q = 1) : d80229 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8068, d80229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8068, d80229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8069 q = 1) (hb : d77844 q = 1) : d80230 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8069, d80230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8069, d80230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8108 q = 1) (hb : d77844 q = 1) : d80251 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8108, d80251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8108, d80251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16554 (p : Pattern) (ha : d8112 p = 1) (hb : d77844 p = 1) : d80255 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8077 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8039 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8078 q = 1) (hb : d77844 q = 1) : d80235 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8078, d77844, d80235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d8078, d77844, d80235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8079 q = 1) (hb : d77844 q = 1) : d80236 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8079, d80236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8079, d80236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8080 q = 1) (hb : d77844 q = 1) : d80237 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8080, d80237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8080, d80237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8112 q = 1) (hb : d77844 q = 1) : d80255 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8112, d80255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8112, d80255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16555 (p : Pattern) (ha : d8117 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8039 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8093 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8093, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d8093, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8094 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8095 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8117 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16556 (p : Pattern) (ha : d77845 p = 1) (hb : d85642 p = 1) : d110208 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2129 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8064 q = 1) (hb : d77845 q = 1) : d80225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8064, d77845, d80225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16547 q ha hb
    | true =>
      simp only [d8064, d77845, d80225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d8065 q = 1) (hb : d77845 q = 1) : d80226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8065, d80226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8065, d80226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8066 q = 1) (hb : d77845 q = 1) : d80227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8066, d80227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8066, d80227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8067 q = 1) (hb : d77845 q = 1) : d80228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8067, d80228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8067, d80228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d2139 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8071 q = 1) (hb : d77845 q = 1) : d80232 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8071, d77845, d80232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16548 q ha hb
    | true =>
      simp only [d8071, d77845, d80232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d8072 q = 1) (hb : d77845 q = 1) : d80233 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8072, d80233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8072, d80233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8073 q = 1) (hb : d77845 q = 1) : d80234 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8073, d80234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8073, d80234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d8043 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d8082 q = 1) (hb : d77845 q = 1) : d80239 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8082, d77845, d80239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16549 q ha hb
    | true =>
      simp only [d8082, d77845, d80239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d85633 q = 1) : d80240 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85633, d80240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85633, d80240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d8097 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8097, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16550 q ha hb
    | true =>
      simp only [d8097, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d8098 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d8098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85634 q = 1) : d110201 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85634, d110201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85634, d110201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d77845 q = 1) (hb : d85635 q = 1) : d110202 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85635, d110202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85635, d110202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77845 q = 1) (hb : d85636 q = 1) : d110203 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85636, d110203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85636, d110203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d2282 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d8104 q = 1) (hb : d77845 q = 1) : d80247 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8104, d77845, d80247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16552 q ha hb
    | true =>
      simp only [d8104, d77845, d80247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d8105 q = 1) (hb : d77845 q = 1) : d80248 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8105, d80248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8105, d80248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d8106 q = 1) (hb : d77845 q = 1) : d80249 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8106, d80249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d8106, d80249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d8107 q = 1) (hb : d77845 q = 1) : d80250 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8107, d80250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8107, d80250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d2288 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d8109 q = 1) (hb : d77845 q = 1) : d80252 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8109, d77845, d80252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16553 q ha hb
    | true =>
      simp only [d8109, d77845, d80252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d8110 q = 1) (hb : d77845 q = 1) : d80253 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8110, d80253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8110, d80253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d8111 q = 1) (hb : d77845 q = 1) : d80254 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8111, d80254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d8111, d80254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d8052 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d8113 q = 1) (hb : d77845 q = 1) : d80256 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8113, d77845, d80256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16554 q ha hb
    | true =>
      simp only [d8113, d77845, d80256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d77845 q = 1) (hb : d85638 q = 1) : d80257 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85638, d80257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
    | true =>
      simp only [d85638, d80257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d8118 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8118, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16555 q ha hb
    | true =>
      simp only [d8118, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h32 (q : Pattern) (ha : d8119 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
    | true =>
      simp only [d8119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h33 (q : Pattern) (ha : d77845 q = 1) (hb : d85639 q = 1) : d110205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85639, d110205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d85639, d110205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q hb ha
  have h34 (q : Pattern) (ha : d77845 q = 1) (hb : d85640 q = 1) : d110206 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85640, d110206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
    | true =>
      simp only [d85640, d110206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d77845 q = 1) (hb : d85641 q = 1) : d110207 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85641, d110207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d85641, d110207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  have h36 (q : Pattern) (ha : d77845 q = 1) (hb : d85642 q = 1) : d110208 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85642, d110208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85642, d110208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h35 q ha hb
  exact h36 p ha hb
theorem andIntro16557 (p : Pattern) (ha : d77845 p = 1) (hb : d85649 p = 1) : d110217 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8113 q = 1) (hb : d77845 q = 1) : d80256 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8113, d77845, d80256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16554 q ha hb
    | true =>
      simp only [d8113, d77845, d80256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85638 q = 1) : d80257 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85638, d80257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85638, d80257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8118 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8118, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16555 q ha hb
    | true =>
      simp only [d8118, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8119 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d85639 q = 1) : d110205 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85639, d110205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85639, d110205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85647 q = 1) : d110215 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85647, d110215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85647, d110215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85648 q = 1) : d110216 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85648, d110216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85648, d110216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85649 q = 1) : d110217 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85649, d110217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85649, d110217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16558 (p : Pattern) (ha : d8149 p = 1) (hb : d77844 p = 1) : d80278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8141 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8145 q = 1) (hb : d77842 q = 1) : d8145 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8146 q = 1) (hb : d77844 q = 1) : d80275 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8146, d77844, d80275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d8146, d77844, d80275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8147 q = 1) (hb : d77844 q = 1) : d80276 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8147, d80276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8147, d80276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8148 q = 1) (hb : d77844 q = 1) : d80277 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8148, d80277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8148, d80277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8149 q = 1) (hb : d77844 q = 1) : d80278 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8149, d80278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8149, d80278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16559 (p : Pattern) (ha : d8168 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8165 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8165, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d8165, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8166 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8167 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8168 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16560 (p : Pattern) (ha : d77845 p = 1) (hb : d85659 p = 1) : d110226 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8153 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8154 q = 1) (hb : d77845 q = 1) : d80279 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8154, d77845, d80279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16558 q ha hb
    | true =>
      simp only [d8154, d77845, d80279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85655 q = 1) : d80280 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85655, d80280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85655, d80280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d8169 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8169, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16559 q ha hb
    | true =>
      simp only [d8169, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8170 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d85656 q = 1) : d110223 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85656, d110223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85656, d110223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85657 q = 1) : d110224 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85657, d110224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85657, d110224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85658 q = 1) : d110225 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85658, d110225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85658, d110225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85659 q = 1) : d110226 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85659, d110226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85659, d110226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16561 (p : Pattern) (ha : d77845 p = 1) (hb : d85665 p = 1) : d110232 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8050 q = 1) (hb : d77845 q = 1) : d80211 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8050, d80211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8050, d80211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16543 q ha hb
  have h2 (q : Pattern) (ha : d8051 q = 1) (hb : d77845 q = 1) : d80212 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8051, d80212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8051, d80212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8059 q = 1) (hb : d77845 q = 1) : d80220 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8059, d80220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16543 q ha hb
    | true =>
      simp only [d8059, d80220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16545 q ha hb
  have h4 (q : Pattern) (ha : d8060 q = 1) (hb : d77845 q = 1) : d80221 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8060, d80221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8060, d80221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8061 q = 1) (hb : d77845 q = 1) : d80222 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8061, d80222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8061, d80222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85643 q = 1) : d110209 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85643, d110209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16551 q ha hb
    | true =>
      simp only [d85643, d110209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16556 q ha hb
  have h7 (q : Pattern) (ha : d8126 q = 1) (hb : d77845 q = 1) : d110211 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8126, d110211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16546 q ha hb
    | true =>
      simp only [d8126, d110211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8291 q ha hb
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85644 q = 1) : d110212 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85644, d110212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85644, d110212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85645 q = 1) : d110213 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85645, d110213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85645, d110213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85646 q = 1) : d110214 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85646, d110214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85646, d110214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77845 q = 1) (hb : d85650 q = 1) : d110218 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85650, d110218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85650, d110218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16557 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8292 q ha hb
  have h13 (q : Pattern) (ha : d77845 q = 1) (hb : d85651 q = 1) : d110219 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85651, d110219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85651, d110219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d77845 q = 1) (hb : d85652 q = 1) : d110220 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85652, d110220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85652, d110220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d77845 q = 1) (hb : d85653 q = 1) : d110221 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85653, d110221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85653, d110221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85654 q = 1) : d110222 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85654, d110222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85654, d110222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77845 q = 1) (hb : d85660 q = 1) : d110227 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85660, d110227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85660, d110227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16560 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8294 q ha hb
  have h19 (q : Pattern) (ha : d77845 q = 1) (hb : d85661 q = 1) : d110228 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85661, d110228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85661, d110228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d77845 q = 1) (hb : d85662 q = 1) : d110229 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85662, d110229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d85662, d110229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d77845 q = 1) (hb : d85663 q = 1) : d110230 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85663, d110230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85663, d110230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d77845 q = 1) (hb : d85664 q = 1) : d110231 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85664, d110231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85664, d110231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d77845 q = 1) (hb : d85665 q = 1) : d110232 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85665, d110232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85665, d110232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro16562 (p : Pattern) (ha : d77845 p = 1) (hb : d85671 p = 1) : d110238 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d85666 q = 1) : d110233 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85666, d110233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85666, d110233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16561 q ha hb
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d85667 q = 1) : d110234 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85667, d110234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85667, d110234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85668 q = 1) : d110235 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85668, d110235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85668, d110235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d85669 q = 1) : d110236 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85669, d110236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85669, d110236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d85670 q = 1) : d110237 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85670, d110237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85670, d110237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85671 q = 1) : d110238 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85671, d110238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85671, d110238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16563 (p : Pattern) (ha : d77845 p = 1) (hb : d85677 p = 1) : d110244 p = 1 := by
  have h0 (q : Pattern) (ha : d77845 q = 1) (hb : d85506 q = 1) : d110077 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85506, d110077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16457 q ha hb
    | true =>
      simp only [d85506, d110077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16478 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d85546 q = 1) : d110116 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85546, d110116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85546, d110116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16499 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85547 q = 1) : d110117 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85547, d110117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85547, d110117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d85587 q = 1) : d110156 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85587, d110156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85587, d110156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16520 q ha hb
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d85588 q = 1) : d110157 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85588, d110157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85588, d110157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85589 q = 1) : d110158 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85589, d110158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85589, d110158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d85629 q = 1) : d110197 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85629, d110197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85629, d110197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16541 q ha hb
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85630 q = 1) : d110198 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85630, d110198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85630, d110198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85631 q = 1) : d110199 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85631, d110199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85631, d110199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85632 q = 1) : d110200 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d85632, d110200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85632, d110200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77845 q = 1) (hb : d85672 q = 1) : d110239 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85672, d110239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85672, d110239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16562 q ha hb
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d85673 q = 1) : d110240 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85673, d110240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85673, d110240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77845 q = 1) (hb : d85674 q = 1) : d110241 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85674, d110241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85674, d110241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77845 q = 1) (hb : d85675 q = 1) : d110242 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d85675, d110242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85675, d110242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77845 q = 1) (hb : d85676 q = 1) : d110243 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d85676, d110243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85676, d110243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85677 q = 1) : d110244 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d85677, d110244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85677, d110244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro16564 (p : Pattern) (ha : d77845 p = 1) (hb : d85683 p = 1) : d110250 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d85678 q = 1) : d110245 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d85678, d110245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16563 q ha hb
    | true =>
      simp only [d85678, d110245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d85679 q = 1) : d110246 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d85679, d110246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85679, d110246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85680 q = 1) : d110247 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d85680, d110247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85680, d110247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d85681 q = 1) : d110248 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d85681, d110248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85681, d110248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d85682 q = 1) : d110249 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d85682, d110249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85682, d110249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85683 q = 1) : d110250 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d85683, d110250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85683, d110250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16565 (p : Pattern) (ha : d77845 p = 1) (hb : d85689 p = 1) : d110256 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d85684 q = 1) : d110251 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d85684, d110251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16564 q ha hb
    | true =>
      simp only [d85684, d110251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d85685 q = 1) : d110252 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d85685, d110252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85685, d110252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85686 q = 1) : d110253 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d85686, d110253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85686, d110253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d85687 q = 1) : d110254 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d85687, d110254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85687, d110254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d85688 q = 1) : d110255 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d85688, d110255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85688, d110255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85689 q = 1) : d110256 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d85689, d110256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85689, d110256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16566 (p : Pattern) (ha : d77845 p = 1) (hb : d85695 p = 1) : d110262 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d85690 q = 1) : d110257 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d85690, d110257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16565 q ha hb
    | true =>
      simp only [d85690, d110257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d85691 q = 1) : d110258 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d85691, d110258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85691, d110258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85692 q = 1) : d110259 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d85692, d110259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85692, d110259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d85693 q = 1) : d110260 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d85693, d110260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85693, d110260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d85694 q = 1) : d110261 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d85694, d110261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85694, d110261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85695 q = 1) : d110262 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d85695, d110262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85695, d110262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16567 (p : Pattern) (ha : d77845 p = 1) (hb : d85701 p = 1) : d110268 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d85696 q = 1) : d110263 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d85696, d110263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16566 q ha hb
    | true =>
      simp only [d85696, d110263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d85697 q = 1) : d110264 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d85697, d110264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85697, d110264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85698 q = 1) : d110265 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d85698, d110265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85698, d110265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d85699 q = 1) : d110266 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d85699, d110266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85699, d110266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d85700 q = 1) : d110267 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d85700, d110267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85700, d110267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85701 q = 1) : d110268 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d85701, d110268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85701, d110268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16568 (p : Pattern) (ha : d77845 p = 1) (hb : d85707 p = 1) : d110274 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d85702 q = 1) : d110269 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d85702, d110269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16567 q ha hb
    | true =>
      simp only [d85702, d110269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d85703 q = 1) : d110270 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d85703, d110270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85703, d110270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85704 q = 1) : d110271 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d85704, d110271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85704, d110271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d85705 q = 1) : d110272 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d85705, d110272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85705, d110272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d85706 q = 1) : d110273 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d85706, d110273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85706, d110273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85707 q = 1) : d110274 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d85707, d110274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85707, d110274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16569 (p : Pattern) (ha : d77845 p = 1) (hb : d85713 p = 1) : d110280 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d85708 q = 1) : d110275 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d85708, d110275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16568 q ha hb
    | true =>
      simp only [d85708, d110275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d85709 q = 1) : d110276 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d85709, d110276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85709, d110276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85710 q = 1) : d110277 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d85710, d110277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85710, d110277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d85711 q = 1) : d110278 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d85711, d110278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85711, d110278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d85712 q = 1) : d110279 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d85712, d110279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85712, d110279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85713 q = 1) : d110280 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d85713, d110280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85713, d110280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16570 (p : Pattern) (ha : d77845 p = 1) (hb : d85719 p = 1) : d110286 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d85714 q = 1) : d110281 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d85714, d110281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16569 q ha hb
    | true =>
      simp only [d85714, d110281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d85715 q = 1) : d110282 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d85715, d110282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85715, d110282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85716 q = 1) : d110283 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d85716, d110283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85716, d110283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d85717 q = 1) : d110284 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d85717, d110284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85717, d110284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d85718 q = 1) : d110285 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d85718, d110285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85718, d110285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85719 q = 1) : d110286 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d85719, d110286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85719, d110286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16571 (p : Pattern) (ha : d70812 p = 1) (hb : d79651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51890 q = 1) (hb : d79648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70810 q = 1) (hb : d79649 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70810, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70810, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d70811 q = 1) (hb : d79650 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70811, d79650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70811, d79650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d70812 q = 1) (hb : d79651 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70812, d79651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70812, d79651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16572 (p : Pattern) (ha : d70817 p = 1) (hb : d79657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70812 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70812 q = 1) (hb : d79652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16571 q ha hb
    | true =>
      simp only [d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d70813 q = 1) (hb : d79653 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70813, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70813, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d70814 q = 1) (hb : d79654 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70814, d79654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70814, d79654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70815 q = 1) (hb : d79655 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70815, d79655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70815, d79655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70816 q = 1) (hb : d79656 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70816, d79656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70816, d79656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70817 q = 1) (hb : d79657 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70817, d79657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70817, d79657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16573 (p : Pattern) (ha : d70818 p = 1) (hb : d79658 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51890 q = 1) (hb : d79648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70810 q = 1) (hb : d79649 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70810, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70810, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d70811 q = 1) (hb : d79650 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70811, d79650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70811, d79650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d70818 q = 1) (hb : d79658 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70818, d79658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70818, d79658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro16574 (p : Pattern) (ha : d70823 p = 1) (hb : d79664 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70812 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70812 q = 1) (hb : d79652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16571 q ha hb
    | true =>
      simp only [d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d70813 q = 1) (hb : d79653 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70813, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70813, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d70814 q = 1) (hb : d79654 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70814, d79654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70814, d79654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70815 q = 1) (hb : d79655 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70815, d79655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70815, d79655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70816 q = 1) (hb : d79656 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70816, d79656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70816, d79656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d70818 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d70818 q = 1) (hb : d79659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16573 q ha hb
    | true =>
      simp only [d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d70819 q = 1) (hb : d79660 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70819, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70819, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d70820 q = 1) (hb : d79661 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70820, d79661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70820, d79661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d70821 q = 1) (hb : d79662 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70821, d79662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70821, d79662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d70822 q = 1) (hb : d79663 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70822, d79663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70822, d79663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d70823 q = 1) (hb : d79664 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70823, d79664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70823, d79664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16575 (p : Pattern) (ha : d70828 p = 1) (hb : d79669 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70818 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70818 q = 1) (hb : d79659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16573 q ha hb
    | true =>
      simp only [d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d70819 q = 1) (hb : d79660 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70819, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70819, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d70820 q = 1) (hb : d79661 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70820, d79661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70820, d79661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70821 q = 1) (hb : d79662 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70821, d79662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70821, d79662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70822 q = 1) (hb : d79663 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70822, d79663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70822, d79663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70828 q = 1) (hb : d79669 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70828, d79669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70828, d79669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16576 (p : Pattern) (ha : d70836 p = 1) (hb : d79678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d78 q = 1) (hb : d51930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11 q ha hb
    | true =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d79 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51931 q = 1) (hb : d79675 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70834 q = 1) (hb : d79676 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70834, d79676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70834, d79676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d70835 q = 1) (hb : d79677 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70835, d79677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70835, d79677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d70836 q = 1) (hb : d79678 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70836, d79678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70836, d79678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro16577 (p : Pattern) (ha : d70841 p = 1) (hb : d79684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70836 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70836 q = 1) (hb : d79679 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16576 q ha hb
    | true =>
      simp only [d79679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d70837 q = 1) (hb : d79680 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70837, d79680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70837, d79680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d70838 q = 1) (hb : d79681 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70838, d79681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70838, d79681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70839 q = 1) (hb : d79682 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70839, d79682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70839, d79682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70840 q = 1) (hb : d79683 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70840, d79683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70840, d79683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70841 q = 1) (hb : d79684 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70841, d79684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70841, d79684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16578 (p : Pattern) (ha : d70847 p = 1) (hb : d79690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70824 q = 1) (hb : d79665 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70824, d79665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16572 q ha hb
    | true =>
      simp only [d70824, d79665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16574 q ha hb
  have h2 (q : Pattern) (ha : d70825 q = 1) (hb : d79666 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70825, d79666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70825, d79666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d70826 q = 1) (hb : d79667 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70826, d79667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70826, d79667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d70827 q = 1) (hb : d79668 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70827, d79668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70827, d79668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70829 q = 1) (hb : d79670 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70829, d79670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70829, d79670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16575 q ha hb
  have h6 (q : Pattern) (ha : d70830 q = 1) (hb : d79671 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70830, d79671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70830, d79671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d70831 q = 1) (hb : d79672 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70831, d79672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70831, d79672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d70832 q = 1) (hb : d79673 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70832, d79673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d70832, d79673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d70833 q = 1) (hb : d79674 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70833, d79674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70833, d79674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70842 q = 1) (hb : d79685 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70842, d79685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70842, d79685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16577 q ha hb
  have h11 (q : Pattern) (ha : d70843 q = 1) (hb : d79686 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70843, d79686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d70843, d79686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d70844 q = 1) (hb : d79687 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70844, d79687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d70844, d79687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d70845 q = 1) (hb : d79688 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d70845, d79688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d70845, d79688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d70846 q = 1) (hb : d79689 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d70846, d79689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d70846, d79689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d70847 q = 1) (hb : d79690 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d70847, d79690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70847, d79690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16579 (p : Pattern) (ha : d70857 p = 1) (hb : d79700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70812 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70812 q = 1) (hb : d79652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16571 q ha hb
    | true =>
      simp only [d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d70853 q = 1) (hb : d79696 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70853, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70853, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70854 q = 1) (hb : d79697 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70854, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70854, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70855 q = 1) (hb : d79698 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70855, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70855, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70856 q = 1) (hb : d79699 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70856, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70856, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70857 q = 1) (hb : d79700 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70857, d79700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70857, d79700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16580 (p : Pattern) (ha : d70864 p = 1) (hb : d79707 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70812 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70812 q = 1) (hb : d79652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16571 q ha hb
    | true =>
      simp only [d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d70853 q = 1) (hb : d79696 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70853, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70853, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70854 q = 1) (hb : d79697 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70854, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70854, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70855 q = 1) (hb : d79698 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70855, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70855, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70856 q = 1) (hb : d79699 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70856, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70856, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d70818 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d70818 q = 1) (hb : d79659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16573 q ha hb
    | true =>
      simp only [d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d70860 q = 1) (hb : d79703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70860, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70860, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70861 q = 1) (hb : d79704 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70861, d79704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70861, d79704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d70862 q = 1) (hb : d79705 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70862, d79705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70862, d79705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d70863 q = 1) (hb : d79706 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70863, d79706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70863, d79706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d70864 q = 1) (hb : d79707 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70864, d79707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70864, d79707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16581 (p : Pattern) (ha : d70869 p = 1) (hb : d79712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51890 q = 1) (hb : d79648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70810 q = 1) (hb : d79649 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70810, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70810, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d70868 q = 1) (hb : d79711 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70868, d79711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70868, d79711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70869 q = 1) (hb : d79712 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70869, d79712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70869, d79712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16582 (p : Pattern) (ha : d70875 p = 1) (hb : d79719 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51890 q = 1) (hb : d79648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70873 q = 1) (hb : d79717 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70873, d79717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70873, d79717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70874 q = 1) (hb : d79718 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70874, d79718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70874, d79718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d70875 q = 1) (hb : d79719 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70875, d79719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70875, d79719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16583 (p : Pattern) (ha : d70880 p = 1) (hb : d79726 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7242 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11697 q ha hb
    | true =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7243 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52003 q = 1) (hb : d79723 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70878 q = 1) (hb : d79724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70878, d79724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70878, d79724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d70879 q = 1) (hb : d79725 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70879, d79725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70879, d79725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d70880 q = 1) (hb : d79726 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70880, d79726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70880, d79726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16584 (p : Pattern) (ha : d109668 p = 1) (hb : d110004 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70869 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70869 q = 1) (hb : d79713 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16581 q ha hb
    | true =>
      simp only [d79713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d70870 q = 1) (hb : d79714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70870, d79714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70870, d79714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70871 q = 1) (hb : d79715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70871, d79715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70871, d79715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70872 q = 1) (hb : d79716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70872, d79716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70872, d79716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70875 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d70875 q = 1) (hb : d79720 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16582 q ha hb
    | true =>
      simp only [d79720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d70876 q = 1) (hb : d79721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70876, d79721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70876, d79721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70877 q = 1) (hb : d79722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70877, d79722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70877, d79722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70880 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d70880 q = 1) (hb : d79727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16583 q ha hb
    | true =>
      simp only [d79727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d70812 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d70881 q = 1) (hb : d79728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70881, d79728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d70881, d79728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d109665 q = 1) (hb : d110001 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109665, d110001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109665, d110001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d109666 q = 1) (hb : d110002 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109666, d110002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109666, d110002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109667 q = 1) (hb : d110003 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109667, d110003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109667, d110003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109668 q = 1) (hb : d110004 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109668, d110004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109668, d110004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16585 (p : Pattern) (ha : d70886 p = 1) (hb : d79733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51890 q = 1) (hb : d79648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70810 q = 1) (hb : d79649 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70810, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70810, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d70868 q = 1) (hb : d79711 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70868, d79711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70868, d79711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70886 q = 1) (hb : d79733 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70886, d79733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70886, d79733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro16586 (p : Pattern) (ha : d70890 p = 1) (hb : d79738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d51890 q = 1) (hb : d79648 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70873 q = 1) (hb : d79717 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70873, d79717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70873, d79717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70874 q = 1) (hb : d79718 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70874, d79718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70874, d79718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d70890 q = 1) (hb : d79738 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70890, d79738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70890, d79738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro16587 (p : Pattern) (ha : d70893 p = 1) (hb : d79742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7242 q = 1) (hb : d52002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11697 q ha hb
    | true =>
      simp only [d7242, d52002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7243 q = 1) (hb : d52003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7243, d52003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52003 q = 1) (hb : d79723 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70878 q = 1) (hb : d79724 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70878, d79724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70878, d79724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d70879 q = 1) (hb : d79725 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70879, d79725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70879, d79725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d70893 q = 1) (hb : d79742 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70893, d79742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70893, d79742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro16588 (p : Pattern) (ha : d109672 p = 1) (hb : d110008 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70869 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70869 q = 1) (hb : d79713 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16581 q ha hb
    | true =>
      simp only [d79713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d70870 q = 1) (hb : d79714 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70870, d79714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70870, d79714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70871 q = 1) (hb : d79715 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70871, d79715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70871, d79715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70872 q = 1) (hb : d79716 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70872, d79716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70872, d79716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70875 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d70875 q = 1) (hb : d79720 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16582 q ha hb
    | true =>
      simp only [d79720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d70876 q = 1) (hb : d79721 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70876, d79721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70876, d79721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70877 q = 1) (hb : d79722 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70877, d79722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70877, d79722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70880 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d70880 q = 1) (hb : d79727 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16583 q ha hb
    | true =>
      simp only [d79727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d70812 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d70881 q = 1) (hb : d79728 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70881, d79728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d70881, d79728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d109665 q = 1) (hb : d110001 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109665, d110001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109665, d110001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d109666 q = 1) (hb : d110002 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109666, d110002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109666, d110002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109667 q = 1) (hb : d110003 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109667, d110003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109667, d110003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d70886 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d70886 q = 1) (hb : d79734 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16585 q ha hb
    | true =>
      simp only [d79734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d70887 q = 1) (hb : d79735 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70887, d79735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70887, d79735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d70888 q = 1) (hb : d79736 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70888, d79736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d70888, d79736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d70889 q = 1) (hb : d79737 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70889, d79737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70889, d79737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d70890 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d70890 q = 1) (hb : d79739 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16586 q ha hb
    | true =>
      simp only [d79739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d70891 q = 1) (hb : d79740 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70891, d79740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70891, d79740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d70892 q = 1) (hb : d79741 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70892, d79741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d70892, d79741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d70893 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d70893 q = 1) (hb : d79743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16587 q ha hb
    | true =>
      simp only [d79743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d70818 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d70894 q = 1) (hb : d79744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70894, d79744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d70894, d79744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d109669 q = 1) (hb : d110005 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109669, d110005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
    | true =>
      simp only [d109669, d110005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d109670 q = 1) (hb : d110006 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109670, d110006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d109670, d110006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d109671 q = 1) (hb : d110007 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109671, d110007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d109671, d110007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d109672 q = 1) (hb : d110008 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109672, d110008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109672, d110008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro16589 (p : Pattern) (ha : d109674 p = 1) (hb : d110010 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70812 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70812 q = 1) (hb : d79652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16571 q ha hb
    | true =>
      simp only [d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d70853 q = 1) (hb : d79696 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70853, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70853, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70854 q = 1) (hb : d79697 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70854, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70854, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70855 q = 1) (hb : d79698 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70855, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70855, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70856 q = 1) (hb : d79699 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70856, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70856, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109674 q = 1) (hb : d110010 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109674, d110010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109674, d110010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro16590 (p : Pattern) (ha : d109681 p = 1) (hb : d110017 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70893 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70893 q = 1) (hb : d79743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16587 q ha hb
    | true =>
      simp only [d79743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70818 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70894 q = 1) (hb : d79744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70894, d79744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70894, d79744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d109669 q = 1) (hb : d110005 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109669, d110005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109669, d110005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d109679 q = 1) (hb : d110015 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109679, d110015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109679, d110015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109680 q = 1) (hb : d110016 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109680, d110016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109680, d110016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109681 q = 1) (hb : d110017 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109681, d110017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109681, d110017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16591 (p : Pattern) (ha : d70913 p = 1) (hb : d79764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7275 q = 1) (hb : d52056 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7275, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11703 q ha hb
    | true =>
      simp only [d7275, d52056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7276 q = 1) (hb : d52057 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7276, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7276, d52057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52057 q = 1) (hb : d79761 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70911 q = 1) (hb : d79762 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70911, d79762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70911, d79762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d70912 q = 1) (hb : d79763 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70912, d79763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70912, d79763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d70913 q = 1) (hb : d79764 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70913, d79764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70913, d79764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro16592 (p : Pattern) (ha : d109690 p = 1) (hb : d110026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70913 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70913 q = 1) (hb : d79765 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16591 q ha hb
    | true =>
      simp only [d79765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70836 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70914 q = 1) (hb : d79766 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70914, d79766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70914, d79766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d109687 q = 1) (hb : d110023 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109687, d110023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109687, d110023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d109688 q = 1) (hb : d110024 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109688, d110024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109688, d110024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109689 q = 1) (hb : d110025 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109689, d110025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109689, d110025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109690 q = 1) (hb : d110026 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109690, d110026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109690, d110026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16593 (p : Pattern) (ha : d109696 p = 1) (hb : d110032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70858 q = 1) (hb : d79701 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70858, d79701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70858, d79701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16579 q ha hb
  have h2 (q : Pattern) (ha : d70859 q = 1) (hb : d79702 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70859, d79702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70859, d79702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d70865 q = 1) (hb : d79708 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70865, d79708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16579 q ha hb
    | true =>
      simp only [d70865, d79708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16580 q ha hb
  have h4 (q : Pattern) (ha : d70866 q = 1) (hb : d79709 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70866, d79709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70866, d79709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70867 q = 1) (hb : d79710 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70867, d79710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70867, d79710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109673 q = 1) (hb : d110009 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109673, d110009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16584 q ha hb
    | true =>
      simp only [d109673, d110009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16588 q ha hb
  have h7 (q : Pattern) (ha : d109675 q = 1) (hb : d110011 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109675, d110011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16589 q ha hb
    | true =>
      simp only [d109675, d110011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d109676 q = 1) (hb : d110012 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109676, d110012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109676, d110012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109677 q = 1) (hb : d110013 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109677, d110013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d109677, d110013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d109678 q = 1) (hb : d110014 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109678, d110014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109678, d110014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109682 q = 1) (hb : d110018 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109682, d110018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109682, d110018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16590 q ha hb
  have h12 (q : Pattern) (ha : d109683 q = 1) (hb : d110019 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109683, d110019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109683, d110019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d109684 q = 1) (hb : d110020 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109684, d110020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109684, d110020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d109685 q = 1) (hb : d110021 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109685, d110021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109685, d110021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d109686 q = 1) (hb : d110022 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109686, d110022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109686, d110022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109691 q = 1) (hb : d110027 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109691, d110027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109691, d110027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16592 q ha hb
  have h17 (q : Pattern) (ha : d109692 q = 1) (hb : d110028 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109692, d110028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109692, d110028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d109693 q = 1) (hb : d110029 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109693, d110029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109693, d110029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d109694 q = 1) (hb : d110030 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109694, d110030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d109694, d110030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d109695 q = 1) (hb : d110031 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109695, d110031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d109695, d110031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d109696 q = 1) (hb : d110032 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109696, d110032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109696, d110032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro16594 (p : Pattern) (ha : d109702 p = 1) (hb : d110038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70848 q = 1) (hb : d79691 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d70848, d79691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70848, d79691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16578 q ha hb
  have h2 (q : Pattern) (ha : d70849 q = 1) (hb : d79692 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d70849, d79692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70849, d79692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d70850 q = 1) (hb : d79693 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d70850, d79693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70850, d79693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70851 q = 1) (hb : d79694 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d70851, d79694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70851, d79694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d70852 q = 1) (hb : d79695 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d70852, d79695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70852, d79695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109697 q = 1) (hb : d110033 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109697, d110033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109697, d110033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16593 q ha hb
  have h7 (q : Pattern) (ha : d109698 q = 1) (hb : d110034 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109698, d110034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109698, d110034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109699 q = 1) (hb : d110035 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109699, d110035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109699, d110035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109700 q = 1) (hb : d110036 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109700, d110036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109700, d110036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109701 q = 1) (hb : d110037 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109701, d110037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109701, d110037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109702 q = 1) (hb : d110038 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109702, d110038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109702, d110038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro16595 (p : Pattern) (ha : d70933 p = 1) (hb : d79786 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52230 q = 1) (hb : d79783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70931 q = 1) (hb : d79784 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70931, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70931, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d70932 q = 1) (hb : d79785 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70932, d79785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70932, d79785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d70933 q = 1) (hb : d79786 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70933, d79786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70933, d79786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16596 (p : Pattern) (ha : d70938 p = 1) (hb : d79792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70933 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70933 q = 1) (hb : d79787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16595 q ha hb
    | true =>
      simp only [d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d70934 q = 1) (hb : d79788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70934, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70934, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70935 q = 1) (hb : d79789 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70935, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70935, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70936 q = 1) (hb : d79790 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70936, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70936, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70937 q = 1) (hb : d79791 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70937, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70937, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70938 q = 1) (hb : d79792 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70938, d79792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70938, d79792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16597 (p : Pattern) (ha : d70941 p = 1) (hb : d79795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52230 q = 1) (hb : d79783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70931 q = 1) (hb : d79784 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70931, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70931, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d70932 q = 1) (hb : d79785 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70932, d79785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70932, d79785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d70941 q = 1) (hb : d79795 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70941, d79795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70941, d79795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro16598 (p : Pattern) (ha : d70946 p = 1) (hb : d79801 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70933 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70933 q = 1) (hb : d79787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16595 q ha hb
    | true =>
      simp only [d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d70934 q = 1) (hb : d79788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70934, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70934, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70935 q = 1) (hb : d79789 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70935, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70935, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70936 q = 1) (hb : d79790 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70936, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70936, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70937 q = 1) (hb : d79791 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70937, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70937, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d70941 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d70941 q = 1) (hb : d79796 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16597 q ha hb
    | true =>
      simp only [d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d70942 q = 1) (hb : d79797 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70942, d79797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70942, d79797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d70943 q = 1) (hb : d79798 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70943, d79798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d70943, d79798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d70944 q = 1) (hb : d79799 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70944, d79799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70944, d79799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d70945 q = 1) (hb : d79800 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70945, d79800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70945, d79800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d70946 q = 1) (hb : d79801 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d70946, d79801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70946, d79801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16599 (p : Pattern) (ha : d70951 p = 1) (hb : d79806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52230 q = 1) (hb : d79783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70931 q = 1) (hb : d79784 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70931, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70931, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d70950 q = 1) (hb : d79805 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70950, d79805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70950, d79805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70951 q = 1) (hb : d79806 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70951, d79806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70951, d79806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16600 (p : Pattern) (ha : d70957 p = 1) (hb : d79813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52230 q = 1) (hb : d79783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70955 q = 1) (hb : d79811 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70955, d79811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70955, d79811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70956 q = 1) (hb : d79812 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70956, d79812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70956, d79812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d70957 q = 1) (hb : d79813 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70957, d79813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70957, d79813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16601 (p : Pattern) (ha : d79820 p = 1) (hb : d109705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68922 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7327 q = 1) (hb : d68921 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d68921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15423 q ha hb
    | true =>
      simp only [d7327, d68921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7328 q = 1) (hb : d68922 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d68922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7328, d68922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68922 q = 1) (hb : d79817 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79818 q = 1) (hb : d109703 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79818, d109703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d79818, d109703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d79819 q = 1) (hb : d109704 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79819, d109704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79819, d109704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d79820 q = 1) (hb : d109705 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79820, d109705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79820, d109705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16602 (p : Pattern) (ha : d109710 p = 1) (hb : d110042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70951 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70951 q = 1) (hb : d79807 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16599 q ha hb
    | true =>
      simp only [d79807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d70952 q = 1) (hb : d79808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70952, d79808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70952, d79808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70953 q = 1) (hb : d79809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70953, d79809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70953, d79809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70954 q = 1) (hb : d79810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70954, d79810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70954, d79810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70957 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d70957 q = 1) (hb : d79814 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16600 q ha hb
    | true =>
      simp only [d79814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d70958 q = 1) (hb : d79815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70958, d79815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70958, d79815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70959 q = 1) (hb : d79816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70959, d79816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70959, d79816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d109705 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d79821 q = 1) (hb : d109705 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16601 q ha hb
    | true =>
      simp only [d79821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d70933 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d79822 q = 1) (hb : d109706 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79822, d109706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79822, d109706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109707 q = 1) (hb : d110039 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109707, d110039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d109707, d110039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d109708 q = 1) (hb : d110040 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109708, d110040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109708, d110040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109709 q = 1) (hb : d110041 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109709, d110041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109709, d110041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109710 q = 1) (hb : d110042 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109710, d110042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109710, d110042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16603 (p : Pattern) (ha : d70969 p = 1) (hb : d79828 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52230 q = 1) (hb : d79783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70931 q = 1) (hb : d79784 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70931, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70931, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d70950 q = 1) (hb : d79805 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70950, d79805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70950, d79805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d70969 q = 1) (hb : d79828 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70969, d79828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70969, d79828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro16604 (p : Pattern) (ha : d70973 p = 1) (hb : d79833 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d482 q = 1) (hb : d52229 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro61 q ha hb
    | true =>
      simp only [d482, d52229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d483 q = 1) (hb : d52230 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d483, d52230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52230 q = 1) (hb : d79783 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70955 q = 1) (hb : d79811 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70955, d79811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70955, d79811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70956 q = 1) (hb : d79812 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70956, d79812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70956, d79812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d70973 q = 1) (hb : d79833 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d70973, d79833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d70973, d79833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro16605 (p : Pattern) (ha : d79837 p = 1) (hb : d109711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d68922 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7327 q = 1) (hb : d68921 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7327, d68921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15423 q ha hb
    | true =>
      simp only [d7327, d68921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7328 q = 1) (hb : d68922 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7328, d68922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7328, d68922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68922 q = 1) (hb : d79817 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79818 q = 1) (hb : d109703 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79818, d109703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d79818, d109703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d79819 q = 1) (hb : d109704 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79819, d109704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79819, d109704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d79837 q = 1) (hb : d109711 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79837, d109711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79837, d109711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro16606 (p : Pattern) (ha : d109716 p = 1) (hb : d110046 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70951 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70951 q = 1) (hb : d79807 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16599 q ha hb
    | true =>
      simp only [d79807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d70952 q = 1) (hb : d79808 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70952, d79808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70952, d79808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70953 q = 1) (hb : d79809 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70953, d79809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70953, d79809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70954 q = 1) (hb : d79810 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70954, d79810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70954, d79810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d70957 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d70957 q = 1) (hb : d79814 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16600 q ha hb
    | true =>
      simp only [d79814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d70958 q = 1) (hb : d79815 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70958, d79815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70958, d79815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d70959 q = 1) (hb : d79816 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70959, d79816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d70959, d79816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d109705 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d79821 q = 1) (hb : d109705 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16601 q ha hb
    | true =>
      simp only [d79821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d70933 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d79822 q = 1) (hb : d109706 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79822, d109706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79822, d109706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109707 q = 1) (hb : d110039 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109707, d110039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d109707, d110039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d109708 q = 1) (hb : d110040 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109708, d110040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109708, d110040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109709 q = 1) (hb : d110041 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109709, d110041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109709, d110041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d70969 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d70969 q = 1) (hb : d79829 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16603 q ha hb
    | true =>
      simp only [d79829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d70970 q = 1) (hb : d79830 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70970, d79830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70970, d79830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d70971 q = 1) (hb : d79831 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70971, d79831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d70971, d79831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d70972 q = 1) (hb : d79832 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70972, d79832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70972, d79832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d70973 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d70973 q = 1) (hb : d79834 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16604 q ha hb
    | true =>
      simp only [d79834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d70974 q = 1) (hb : d79835 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70974, d79835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70974, d79835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d70975 q = 1) (hb : d79836 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70975, d79836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d70975, d79836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d109711 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d79838 q = 1) (hb : d109711 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16605 q ha hb
    | true =>
      simp only [d79838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d70941 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d79839 q = 1) (hb : d109712 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79839, d109712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d79839, d109712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d109713 q = 1) (hb : d110043 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109713, d110043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
    | true =>
      simp only [d109713, d110043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d109714 q = 1) (hb : d110044 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109714, d110044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d109714, d110044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d109715 q = 1) (hb : d110045 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109715, d110045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d109715, d110045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d109716 q = 1) (hb : d110046 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109716, d110046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109716, d110046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro16607 (p : Pattern) (ha : d109718 p = 1) (hb : d110048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70933 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d70933 q = 1) (hb : d79787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16595 q ha hb
    | true =>
      simp only [d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d70934 q = 1) (hb : d79788 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70934, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70934, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d70935 q = 1) (hb : d79789 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d70935, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70935, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70936 q = 1) (hb : d79790 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d70936, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70936, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d70937 q = 1) (hb : d79791 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d70937, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70937, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109718 q = 1) (hb : d110048 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109718, d110048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109718, d110048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro16608 (p : Pattern) (ha : d109725 p = 1) (hb : d110055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109711 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79838 q = 1) (hb : d109711 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16605 q ha hb
    | true =>
      simp only [d79838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70941 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79839 q = 1) (hb : d109712 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79839, d109712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79839, d109712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109713 q = 1) (hb : d110043 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109713, d110043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d109713, d110043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d109723 q = 1) (hb : d110053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109723, d110053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109723, d110053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109724 q = 1) (hb : d110054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109724, d110054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109724, d110054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109725 q = 1) (hb : d110055 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109725, d110055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109725, d110055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16609 (p : Pattern) (ha : d79860 p = 1) (hb : d109733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75848 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7391 q = 1) (hb : d75847 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7391, d75847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15436 q ha hb
    | true =>
      simp only [d7391, d75847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7392 q = 1) (hb : d75848 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7392, d75848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7392, d75848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75848 q = 1) (hb : d79857 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79858 q = 1) (hb : d109731 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79858, d109731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d79858, d109731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d79859 q = 1) (hb : d109732 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79859, d109732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79859, d109732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d79860 q = 1) (hb : d109733 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79860, d109733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79860, d109733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro16610 (p : Pattern) (ha : d109738 p = 1) (hb : d110064 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109733 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79861 q = 1) (hb : d109733 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16609 q ha hb
    | true =>
      simp only [d79861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71000 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79862 q = 1) (hb : d109734 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79862, d109734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79862, d109734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109735 q = 1) (hb : d110061 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109735, d110061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d109735, d110061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d109736 q = 1) (hb : d110062 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109736, d110062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109736, d110062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109737 q = 1) (hb : d110063 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109737, d110063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109737, d110063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109738 q = 1) (hb : d110064 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109738, d110064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109738, d110064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16611 (p : Pattern) (ha : d109744 p = 1) (hb : d110070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d70939 q = 1) (hb : d79793 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70939, d79793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d70939, d79793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16596 q ha hb
  have h2 (q : Pattern) (ha : d70940 q = 1) (hb : d79794 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70940, d79794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d70940, d79794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d70947 q = 1) (hb : d79802 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d70947, d79802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16596 q ha hb
    | true =>
      simp only [d70947, d79802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16598 q ha hb
  have h4 (q : Pattern) (ha : d70948 q = 1) (hb : d79803 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d70948, d79803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d70948, d79803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d70949 q = 1) (hb : d79804 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d70949, d79804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d70949, d79804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109717 q = 1) (hb : d110047 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109717, d110047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16602 q ha hb
    | true =>
      simp only [d109717, d110047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16606 q ha hb
  have h7 (q : Pattern) (ha : d109719 q = 1) (hb : d110049 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109719, d110049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16607 q ha hb
    | true =>
      simp only [d109719, d110049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d109720 q = 1) (hb : d110050 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109720, d110050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109720, d110050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109721 q = 1) (hb : d110051 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109721, d110051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d109721, d110051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d109722 q = 1) (hb : d110052 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109722, d110052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109722, d110052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109726 q = 1) (hb : d110056 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109726, d110056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109726, d110056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16608 q ha hb
  have h12 (q : Pattern) (ha : d109727 q = 1) (hb : d110057 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109727, d110057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109727, d110057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d109728 q = 1) (hb : d110058 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109728, d110058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109728, d110058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d109729 q = 1) (hb : d110059 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109729, d110059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109729, d110059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d109730 q = 1) (hb : d110060 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109730, d110060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109730, d110060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109739 q = 1) (hb : d110065 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109739, d110065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109739, d110065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16610 q ha hb
  have h17 (q : Pattern) (ha : d109740 q = 1) (hb : d110066 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109740, d110066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109740, d110066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d109741 q = 1) (hb : d110067 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109741, d110067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109741, d110067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d109742 q = 1) (hb : d110068 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109742, d110068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d109742, d110068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d109743 q = 1) (hb : d110069 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109743, d110069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d109743, d110069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d109744 q = 1) (hb : d110070 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109744, d110070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109744, d110070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro16612 (p : Pattern) (ha : d109750 p = 1) (hb : d110076 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109745 q = 1) (hb : d110071 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109745, d110071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109745, d110071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16611 q ha hb
  have h2 (q : Pattern) (ha : d109746 q = 1) (hb : d110072 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109746, d110072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109746, d110072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109747 q = 1) (hb : d110073 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109747, d110073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109747, d110073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109748 q = 1) (hb : d110074 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109748, d110074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109748, d110074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109749 q = 1) (hb : d110075 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109749, d110075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109749, d110075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109750 q = 1) (hb : d110076 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109750, d110076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109750, d110076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16613 (p : Pattern) (ha : d71022 p = 1) (hb : d79889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52452 q = 1) (hb : d79886 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71020 q = 1) (hb : d79887 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71020, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71020, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71021 q = 1) (hb : d79888 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71021, d79888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71021, d79888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d71022 q = 1) (hb : d79889 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71022, d79889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71022, d79889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16614 (p : Pattern) (ha : d71027 p = 1) (hb : d79895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71022 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71022 q = 1) (hb : d79890 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16613 q ha hb
    | true =>
      simp only [d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d71023 q = 1) (hb : d79891 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71023, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71023, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71024 q = 1) (hb : d79892 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71024, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71024, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71025 q = 1) (hb : d79893 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71025, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71025, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71026 q = 1) (hb : d79894 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71026, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71026, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71027 q = 1) (hb : d79895 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71027, d79895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71027, d79895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16615 (p : Pattern) (ha : d71030 p = 1) (hb : d79898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52452 q = 1) (hb : d79886 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71020 q = 1) (hb : d79887 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71020, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71020, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d71021 q = 1) (hb : d79888 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71021, d79888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71021, d79888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d71030 q = 1) (hb : d79898 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71030, d79898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71030, d79898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro16616 (p : Pattern) (ha : d71035 p = 1) (hb : d79904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71022 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71022 q = 1) (hb : d79890 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16613 q ha hb
    | true =>
      simp only [d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d71023 q = 1) (hb : d79891 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71023, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71023, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71024 q = 1) (hb : d79892 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71024, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71024, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71025 q = 1) (hb : d79893 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71025, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71025, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71026 q = 1) (hb : d79894 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71026, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71026, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d71030 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d71030 q = 1) (hb : d79899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16615 q ha hb
    | true =>
      simp only [d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d71031 q = 1) (hb : d79900 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71031, d79900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71031, d79900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71032 q = 1) (hb : d79901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71032, d79901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71032, d79901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d71033 q = 1) (hb : d79902 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71033, d79902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71033, d79902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d71034 q = 1) (hb : d79903 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71034, d79903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71034, d79903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d71035 q = 1) (hb : d79904 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71035, d79904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71035, d79904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16617 (p : Pattern) (ha : d71040 p = 1) (hb : d79909 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52452 q = 1) (hb : d79886 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71020 q = 1) (hb : d79887 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71020, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71020, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71039 q = 1) (hb : d79908 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71039, d79908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71039, d79908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71040 q = 1) (hb : d79909 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71040, d79909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71040, d79909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16618 (p : Pattern) (ha : d71046 p = 1) (hb : d79916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52452 q = 1) (hb : d79886 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71044 q = 1) (hb : d79914 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71044, d79914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71044, d79914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71045 q = 1) (hb : d79915 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71045, d79915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71045, d79915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d71046 q = 1) (hb : d79916 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71046, d79916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71046, d79916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16619 (p : Pattern) (ha : d79923 p = 1) (hb : d109754 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69014 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7576 q = 1) (hb : d69013 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d69013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15446 q ha hb
    | true =>
      simp only [d7576, d69013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7577 q = 1) (hb : d69014 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d69014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7577, d69014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69014 q = 1) (hb : d79920 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79921 q = 1) (hb : d109752 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79921, d109752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d79921, d109752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d79922 q = 1) (hb : d109753 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79922, d109753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79922, d109753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d79923 q = 1) (hb : d109754 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79923, d109754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79923, d109754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16620 (p : Pattern) (ha : d109759 p = 1) (hb : d110081 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71040 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71040 q = 1) (hb : d79910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16617 q ha hb
    | true =>
      simp only [d79910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d71041 q = 1) (hb : d79911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71041, d79911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71041, d79911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71042 q = 1) (hb : d79912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71042, d79912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71042, d79912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71043 q = 1) (hb : d79913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71043, d79913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71043, d79913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71046 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71046 q = 1) (hb : d79917 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16618 q ha hb
    | true =>
      simp only [d79917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d71047 q = 1) (hb : d79918 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71047, d79918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71047, d79918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71048 q = 1) (hb : d79919 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71048, d79919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71048, d79919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d109754 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d79924 q = 1) (hb : d109754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16619 q ha hb
    | true =>
      simp only [d79924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71022 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d79925 q = 1) (hb : d109755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79925, d109755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79925, d109755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109756 q = 1) (hb : d110078 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109756, d110078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d109756, d110078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d109757 q = 1) (hb : d110079 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109757, d110079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109757, d110079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109758 q = 1) (hb : d110080 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109758, d110080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109758, d110080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109759 q = 1) (hb : d110081 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109759, d110081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109759, d110081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16621 (p : Pattern) (ha : d71058 p = 1) (hb : d79931 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52452 q = 1) (hb : d79886 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71020 q = 1) (hb : d79887 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71020, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71020, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71039 q = 1) (hb : d79908 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71039, d79908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71039, d79908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71058 q = 1) (hb : d79931 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71058, d79931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71058, d79931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro16622 (p : Pattern) (ha : d71062 p = 1) (hb : d79936 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d774 q = 1) (hb : d52451 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro105 q ha hb
    | true =>
      simp only [d774, d52451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d775 q = 1) (hb : d52452 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d52452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52452 q = 1) (hb : d79886 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71044 q = 1) (hb : d79914 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71044, d79914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71044, d79914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71045 q = 1) (hb : d79915 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71045, d79915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71045, d79915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d71062 q = 1) (hb : d79936 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71062, d79936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71062, d79936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro16623 (p : Pattern) (ha : d79940 p = 1) (hb : d109760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69014 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7576 q = 1) (hb : d69013 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7576, d69013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15446 q ha hb
    | true =>
      simp only [d7576, d69013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7577 q = 1) (hb : d69014 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7577, d69014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7577, d69014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69014 q = 1) (hb : d79920 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79921 q = 1) (hb : d109752 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79921, d109752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d79921, d109752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d79922 q = 1) (hb : d109753 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79922, d109753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79922, d109753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d79940 q = 1) (hb : d109760 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79940, d109760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79940, d109760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro16624 (p : Pattern) (ha : d109765 p = 1) (hb : d110085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71040 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71040 q = 1) (hb : d79910 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16617 q ha hb
    | true =>
      simp only [d79910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d71041 q = 1) (hb : d79911 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71041, d79911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71041, d79911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71042 q = 1) (hb : d79912 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71042, d79912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71042, d79912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71043 q = 1) (hb : d79913 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71043, d79913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71043, d79913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71046 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71046 q = 1) (hb : d79917 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16618 q ha hb
    | true =>
      simp only [d79917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d71047 q = 1) (hb : d79918 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71047, d79918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71047, d79918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71048 q = 1) (hb : d79919 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71048, d79919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71048, d79919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d109754 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d79924 q = 1) (hb : d109754 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16619 q ha hb
    | true =>
      simp only [d79924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71022 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d79925 q = 1) (hb : d109755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79925, d109755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79925, d109755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109756 q = 1) (hb : d110078 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109756, d110078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d109756, d110078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d109757 q = 1) (hb : d110079 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109757, d110079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109757, d110079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109758 q = 1) (hb : d110080 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109758, d110080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109758, d110080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d71058 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d71058 q = 1) (hb : d79932 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16621 q ha hb
    | true =>
      simp only [d79932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d71059 q = 1) (hb : d79933 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71059, d79933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71059, d79933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d71060 q = 1) (hb : d79934 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71060, d79934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d71060, d79934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d71061 q = 1) (hb : d79935 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71061, d79935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71061, d79935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d71062 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d71062 q = 1) (hb : d79937 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16622 q ha hb
    | true =>
      simp only [d79937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d71063 q = 1) (hb : d79938 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71063, d79938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71063, d79938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d71064 q = 1) (hb : d79939 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71064, d79939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d71064, d79939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d109760 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d79941 q = 1) (hb : d109760 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16623 q ha hb
    | true =>
      simp only [d79941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d71030 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d79942 q = 1) (hb : d109761 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79942, d109761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d79942, d109761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d109762 q = 1) (hb : d110082 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109762, d110082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
    | true =>
      simp only [d109762, d110082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d109763 q = 1) (hb : d110083 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109763, d110083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d109763, d110083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d109764 q = 1) (hb : d110084 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109764, d110084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d109764, d110084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d109765 q = 1) (hb : d110085 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109765, d110085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109765, d110085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro16625 (p : Pattern) (ha : d109767 p = 1) (hb : d110087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71022 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71022 q = 1) (hb : d79890 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16613 q ha hb
    | true =>
      simp only [d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d71023 q = 1) (hb : d79891 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71023, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71023, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71024 q = 1) (hb : d79892 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71024, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71024, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71025 q = 1) (hb : d79893 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71025, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71025, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71026 q = 1) (hb : d79894 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71026, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71026, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109767 q = 1) (hb : d110087 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109767, d110087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109767, d110087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro16626 (p : Pattern) (ha : d109774 p = 1) (hb : d110094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109760 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79941 q = 1) (hb : d109760 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16623 q ha hb
    | true =>
      simp only [d79941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71030 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79942 q = 1) (hb : d109761 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79942, d109761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79942, d109761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109762 q = 1) (hb : d110082 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109762, d110082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d109762, d110082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d109772 q = 1) (hb : d110092 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109772, d110092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109772, d110092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109773 q = 1) (hb : d110093 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109773, d110093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109773, d110093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109774 q = 1) (hb : d110094 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109774, d110094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109774, d110094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16627 (p : Pattern) (ha : d79963 p = 1) (hb : d109782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d75969 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7682 q = 1) (hb : d75968 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7682, d75968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15459 q ha hb
    | true =>
      simp only [d7682, d75968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7683 q = 1) (hb : d75969 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7683, d75969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7683, d75969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75969 q = 1) (hb : d79960 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79961 q = 1) (hb : d109780 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d79961, d109780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d79961, d109780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d79962 q = 1) (hb : d109781 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d79962, d109781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79962, d109781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d79963 q = 1) (hb : d109782 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d79963, d109782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79963, d109782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro16628 (p : Pattern) (ha : d109787 p = 1) (hb : d110103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109782 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d79964 q = 1) (hb : d109782 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16627 q ha hb
    | true =>
      simp only [d79964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71089 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d79965 q = 1) (hb : d109783 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79965, d109783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79965, d109783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109784 q = 1) (hb : d110100 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109784, d110100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d109784, d110100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d109785 q = 1) (hb : d110101 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109785, d110101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109785, d110101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109786 q = 1) (hb : d110102 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109786, d110102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109786, d110102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109787 q = 1) (hb : d110103 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109787, d110103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109787, d110103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16629 (p : Pattern) (ha : d109793 p = 1) (hb : d110109 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71028 q = 1) (hb : d79896 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71028, d79896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71028, d79896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16614 q ha hb
  have h2 (q : Pattern) (ha : d71029 q = 1) (hb : d79897 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71029, d79897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71029, d79897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71036 q = 1) (hb : d79905 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71036, d79905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16614 q ha hb
    | true =>
      simp only [d71036, d79905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16616 q ha hb
  have h4 (q : Pattern) (ha : d71037 q = 1) (hb : d79906 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71037, d79906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71037, d79906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71038 q = 1) (hb : d79907 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71038, d79907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71038, d79907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109766 q = 1) (hb : d110086 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109766, d110086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16620 q ha hb
    | true =>
      simp only [d109766, d110086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16624 q ha hb
  have h7 (q : Pattern) (ha : d109768 q = 1) (hb : d110088 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109768, d110088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16625 q ha hb
    | true =>
      simp only [d109768, d110088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d109769 q = 1) (hb : d110089 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109769, d110089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109769, d110089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109770 q = 1) (hb : d110090 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109770, d110090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d109770, d110090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d109771 q = 1) (hb : d110091 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109771, d110091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109771, d110091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109775 q = 1) (hb : d110095 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109775, d110095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109775, d110095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16626 q ha hb
  have h12 (q : Pattern) (ha : d109776 q = 1) (hb : d110096 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109776, d110096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109776, d110096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d109777 q = 1) (hb : d110097 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109777, d110097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109777, d110097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d109778 q = 1) (hb : d110098 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109778, d110098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109778, d110098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d109779 q = 1) (hb : d110099 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109779, d110099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109779, d110099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109788 q = 1) (hb : d110104 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109788, d110104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109788, d110104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16628 q ha hb
  have h17 (q : Pattern) (ha : d109789 q = 1) (hb : d110105 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109789, d110105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109789, d110105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d109790 q = 1) (hb : d110106 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109790, d110106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109790, d110106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d109791 q = 1) (hb : d110107 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109791, d110107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d109791, d110107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d109792 q = 1) (hb : d110108 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109792, d110108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d109792, d110108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d109793 q = 1) (hb : d110109 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109793, d110109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109793, d110109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro16630 (p : Pattern) (ha : d109799 p = 1) (hb : d110115 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109794 q = 1) (hb : d110110 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109794, d110110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109794, d110110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16629 q ha hb
  have h2 (q : Pattern) (ha : d109795 q = 1) (hb : d110111 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109795, d110111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109795, d110111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109796 q = 1) (hb : d110112 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109796, d110112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109796, d110112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109797 q = 1) (hb : d110113 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109797, d110113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109797, d110113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109798 q = 1) (hb : d110114 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109798, d110114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109798, d110114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109799 q = 1) (hb : d110115 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109799, d110115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109799, d110115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16631 (p : Pattern) (ha : d71112 p = 1) (hb : d79993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52735 q = 1) (hb : d79990 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71110 q = 1) (hb : d79991 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71110, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71110, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71111 q = 1) (hb : d79992 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71111, d79992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71111, d79992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d71112 q = 1) (hb : d79993 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71112, d79993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71112, d79993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16632 (p : Pattern) (ha : d71117 p = 1) (hb : d79999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71112 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71112 q = 1) (hb : d79994 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16631 q ha hb
    | true =>
      simp only [d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d71113 q = 1) (hb : d79995 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71113, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71113, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71114 q = 1) (hb : d79996 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71114, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71114, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71115 q = 1) (hb : d79997 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71115, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71115, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71116 q = 1) (hb : d79998 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71116, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71116, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71117 q = 1) (hb : d79999 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71117, d79999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71117, d79999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16633 (p : Pattern) (ha : d71120 p = 1) (hb : d80002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52735 q = 1) (hb : d79990 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71110 q = 1) (hb : d79991 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71110, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71110, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d71111 q = 1) (hb : d79992 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71111, d79992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71111, d79992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d71120 q = 1) (hb : d80002 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71120, d80002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71120, d80002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro16634 (p : Pattern) (ha : d71125 p = 1) (hb : d80008 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71112 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71112 q = 1) (hb : d79994 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16631 q ha hb
    | true =>
      simp only [d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d71113 q = 1) (hb : d79995 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71113, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71113, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71114 q = 1) (hb : d79996 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71114, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71114, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71115 q = 1) (hb : d79997 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71115, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71115, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71116 q = 1) (hb : d79998 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71116, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71116, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d71120 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d71120 q = 1) (hb : d80003 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16633 q ha hb
    | true =>
      simp only [d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d71121 q = 1) (hb : d80004 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71121, d80004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71121, d80004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71122 q = 1) (hb : d80005 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71122, d80005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71122, d80005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d71123 q = 1) (hb : d80006 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71123, d80006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71123, d80006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d71124 q = 1) (hb : d80007 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71124, d80007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71124, d80007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d71125 q = 1) (hb : d80008 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71125, d80008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71125, d80008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16635 (p : Pattern) (ha : d71130 p = 1) (hb : d80013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52735 q = 1) (hb : d79990 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71110 q = 1) (hb : d79991 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71110, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71110, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71129 q = 1) (hb : d80012 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71129, d80012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71129, d80012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71130 q = 1) (hb : d80013 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71130, d80013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71130, d80013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16636 (p : Pattern) (ha : d71136 p = 1) (hb : d80020 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52735 q = 1) (hb : d79990 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71134 q = 1) (hb : d80018 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71134, d80018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71134, d80018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71135 q = 1) (hb : d80019 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71135, d80019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71135, d80019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d71136 q = 1) (hb : d80020 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71136, d80020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71136, d80020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16637 (p : Pattern) (ha : d80027 p = 1) (hb : d109804 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69121 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7729 q = 1) (hb : d69120 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d69120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15470 q ha hb
    | true =>
      simp only [d7729, d69120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7730 q = 1) (hb : d69121 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d69121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7730, d69121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69121 q = 1) (hb : d80024 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d80025 q = 1) (hb : d109802 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d80025, d109802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d80025, d109802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80026 q = 1) (hb : d109803 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d80026, d109803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80026, d109803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d80027 q = 1) (hb : d109804 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d80027, d109804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80027, d109804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16638 (p : Pattern) (ha : d109809 p = 1) (hb : d110121 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71130 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71130 q = 1) (hb : d80014 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16635 q ha hb
    | true =>
      simp only [d80014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d71131 q = 1) (hb : d80015 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71131, d80015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71131, d80015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71132 q = 1) (hb : d80016 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71132, d80016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71132, d80016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71133 q = 1) (hb : d80017 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71133, d80017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71133, d80017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71136 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71136 q = 1) (hb : d80021 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16636 q ha hb
    | true =>
      simp only [d80021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d71137 q = 1) (hb : d80022 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71137, d80022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71137, d80022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71138 q = 1) (hb : d80023 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71138, d80023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71138, d80023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d109804 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d80028 q = 1) (hb : d109804 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16637 q ha hb
    | true =>
      simp only [d80028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71112 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d80029 q = 1) (hb : d109805 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80029, d109805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80029, d109805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109806 q = 1) (hb : d110118 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109806, d110118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d109806, d110118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d109807 q = 1) (hb : d110119 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109807, d110119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109807, d110119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109808 q = 1) (hb : d110120 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109808, d110120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109808, d110120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109809 q = 1) (hb : d110121 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109809, d110121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109809, d110121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16639 (p : Pattern) (ha : d71148 p = 1) (hb : d80035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52735 q = 1) (hb : d79990 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71110 q = 1) (hb : d79991 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71110, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71110, d79991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71129 q = 1) (hb : d80012 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71129, d80012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71129, d80012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71148 q = 1) (hb : d80035 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71148, d80035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71148, d80035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro16640 (p : Pattern) (ha : d71152 p = 1) (hb : d80040 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1153 q = 1) (hb : d52734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro157 q ha hb
    | true =>
      simp only [d1153, d52734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1154 q = 1) (hb : d52735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d52735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52735 q = 1) (hb : d79990 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d79990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71134 q = 1) (hb : d80018 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71134, d80018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71134, d80018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71135 q = 1) (hb : d80019 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71135, d80019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71135, d80019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d71152 q = 1) (hb : d80040 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71152, d80040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71152, d80040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro16641 (p : Pattern) (ha : d80044 p = 1) (hb : d109810 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69121 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7729 q = 1) (hb : d69120 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7729, d69120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15470 q ha hb
    | true =>
      simp only [d7729, d69120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7730 q = 1) (hb : d69121 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7730, d69121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7730, d69121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69121 q = 1) (hb : d80024 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d80025 q = 1) (hb : d109802 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d80025, d109802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d80025, d109802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d80026 q = 1) (hb : d109803 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d80026, d109803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80026, d109803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d80044 q = 1) (hb : d109810 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d80044, d109810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80044, d109810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro16642 (p : Pattern) (ha : d109815 p = 1) (hb : d110125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71130 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71130 q = 1) (hb : d80014 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16635 q ha hb
    | true =>
      simp only [d80014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d71131 q = 1) (hb : d80015 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71131, d80015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71131, d80015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71132 q = 1) (hb : d80016 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71132, d80016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71132, d80016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71133 q = 1) (hb : d80017 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71133, d80017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71133, d80017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71136 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71136 q = 1) (hb : d80021 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16636 q ha hb
    | true =>
      simp only [d80021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d71137 q = 1) (hb : d80022 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71137, d80022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71137, d80022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71138 q = 1) (hb : d80023 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71138, d80023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71138, d80023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d109804 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d80028 q = 1) (hb : d109804 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16637 q ha hb
    | true =>
      simp only [d80028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71112 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d80029 q = 1) (hb : d109805 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80029, d109805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80029, d109805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109806 q = 1) (hb : d110118 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109806, d110118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d109806, d110118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d109807 q = 1) (hb : d110119 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109807, d110119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109807, d110119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109808 q = 1) (hb : d110120 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109808, d110120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109808, d110120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d71148 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d71148 q = 1) (hb : d80036 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16639 q ha hb
    | true =>
      simp only [d80036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d71149 q = 1) (hb : d80037 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71149, d80037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71149, d80037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d71150 q = 1) (hb : d80038 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71150, d80038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d71150, d80038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d71151 q = 1) (hb : d80039 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71151, d80039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71151, d80039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d71152 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d71152 q = 1) (hb : d80041 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16640 q ha hb
    | true =>
      simp only [d80041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d71153 q = 1) (hb : d80042 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71153, d80042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71153, d80042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d71154 q = 1) (hb : d80043 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71154, d80043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d71154, d80043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d109810 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d80045 q = 1) (hb : d109810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16641 q ha hb
    | true =>
      simp only [d80045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d71120 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d80046 q = 1) (hb : d109811 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80046, d109811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d80046, d109811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d109812 q = 1) (hb : d110122 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109812, d110122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
    | true =>
      simp only [d109812, d110122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d109813 q = 1) (hb : d110123 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109813, d110123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d109813, d110123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d109814 q = 1) (hb : d110124 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109814, d110124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d109814, d110124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d109815 q = 1) (hb : d110125 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109815, d110125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109815, d110125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro16643 (p : Pattern) (ha : d109817 p = 1) (hb : d110127 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71112 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71112 q = 1) (hb : d79994 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16631 q ha hb
    | true =>
      simp only [d79994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d71113 q = 1) (hb : d79995 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71113, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71113, d79995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71114 q = 1) (hb : d79996 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71114, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71114, d79996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71115 q = 1) (hb : d79997 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71115, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71115, d79997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71116 q = 1) (hb : d79998 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71116, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71116, d79998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109817 q = 1) (hb : d110127 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109817, d110127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109817, d110127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro16644 (p : Pattern) (ha : d109824 p = 1) (hb : d110134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109810 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d80045 q = 1) (hb : d109810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16641 q ha hb
    | true =>
      simp only [d80045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71120 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d80046 q = 1) (hb : d109811 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80046, d109811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80046, d109811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109812 q = 1) (hb : d110122 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109812, d110122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d109812, d110122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d109822 q = 1) (hb : d110132 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109822, d110132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109822, d110132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109823 q = 1) (hb : d110133 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109823, d110133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109823, d110133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109824 q = 1) (hb : d110134 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109824, d110134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109824, d110134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16645 (p : Pattern) (ha : d80067 p = 1) (hb : d109832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76103 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7835 q = 1) (hb : d76102 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7835, d76102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15483 q ha hb
    | true =>
      simp only [d7835, d76102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7836 q = 1) (hb : d76103 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7836, d76103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7836, d76103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76103 q = 1) (hb : d80064 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d80065 q = 1) (hb : d109830 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d80065, d109830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d80065, d109830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d80066 q = 1) (hb : d109831 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d80066, d109831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80066, d109831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d80067 q = 1) (hb : d109832 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d80067, d109832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80067, d109832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro16646 (p : Pattern) (ha : d109837 p = 1) (hb : d110143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109832 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d80068 q = 1) (hb : d109832 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16645 q ha hb
    | true =>
      simp only [d80068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71179 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d80069 q = 1) (hb : d109833 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80069, d109833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80069, d109833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109834 q = 1) (hb : d110140 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109834, d110140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d109834, d110140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d109835 q = 1) (hb : d110141 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109835, d110141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109835, d110141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109836 q = 1) (hb : d110142 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109836, d110142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109836, d110142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109837 q = 1) (hb : d110143 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109837, d110143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109837, d110143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16647 (p : Pattern) (ha : d109843 p = 1) (hb : d110149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71118 q = 1) (hb : d80000 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71118, d80000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71118, d80000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16632 q ha hb
  have h2 (q : Pattern) (ha : d71119 q = 1) (hb : d80001 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71119, d80001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71119, d80001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71126 q = 1) (hb : d80009 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71126, d80009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16632 q ha hb
    | true =>
      simp only [d71126, d80009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16634 q ha hb
  have h4 (q : Pattern) (ha : d71127 q = 1) (hb : d80010 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71127, d80010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71127, d80010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71128 q = 1) (hb : d80011 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71128, d80011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71128, d80011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109816 q = 1) (hb : d110126 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109816, d110126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16638 q ha hb
    | true =>
      simp only [d109816, d110126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16642 q ha hb
  have h7 (q : Pattern) (ha : d109818 q = 1) (hb : d110128 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109818, d110128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16643 q ha hb
    | true =>
      simp only [d109818, d110128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d109819 q = 1) (hb : d110129 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109819, d110129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109819, d110129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109820 q = 1) (hb : d110130 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109820, d110130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d109820, d110130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d109821 q = 1) (hb : d110131 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109821, d110131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109821, d110131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109825 q = 1) (hb : d110135 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109825, d110135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109825, d110135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16644 q ha hb
  have h12 (q : Pattern) (ha : d109826 q = 1) (hb : d110136 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109826, d110136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109826, d110136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d109827 q = 1) (hb : d110137 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109827, d110137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109827, d110137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d109828 q = 1) (hb : d110138 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109828, d110138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109828, d110138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d109829 q = 1) (hb : d110139 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109829, d110139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109829, d110139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109838 q = 1) (hb : d110144 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109838, d110144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109838, d110144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16646 q ha hb
  have h17 (q : Pattern) (ha : d109839 q = 1) (hb : d110145 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109839, d110145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109839, d110145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d109840 q = 1) (hb : d110146 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109840, d110146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109840, d110146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d109841 q = 1) (hb : d110147 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109841, d110147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d109841, d110147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d109842 q = 1) (hb : d110148 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109842, d110148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d109842, d110148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d109843 q = 1) (hb : d110149 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109843, d110149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109843, d110149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro16648 (p : Pattern) (ha : d109849 p = 1) (hb : d110155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109844 q = 1) (hb : d110150 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109844, d110150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109844, d110150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16647 q ha hb
  have h2 (q : Pattern) (ha : d109845 q = 1) (hb : d110151 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109845, d110151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109845, d110151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109846 q = 1) (hb : d110152 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109846, d110152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109846, d110152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109847 q = 1) (hb : d110153 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109847, d110153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109847, d110153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109848 q = 1) (hb : d110154 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109848, d110154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109848, d110154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109849 q = 1) (hb : d110155 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109849, d110155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109849, d110155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16649 (p : Pattern) (ha : d71203 p = 1) (hb : d80098 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53056 q = 1) (hb : d80095 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71201 q = 1) (hb : d80096 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71201, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71201, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71202 q = 1) (hb : d80097 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71202, d80097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71202, d80097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d71203 q = 1) (hb : d80098 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71203, d80098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71203, d80098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16650 (p : Pattern) (ha : d71208 p = 1) (hb : d80104 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71203 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71203 q = 1) (hb : d80099 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16649 q ha hb
    | true =>
      simp only [d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d71204 q = 1) (hb : d80100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71204, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71204, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71205 q = 1) (hb : d80101 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71205, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71205, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71206 q = 1) (hb : d80102 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71206, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71206, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71207 q = 1) (hb : d80103 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71207, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71207, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71208 q = 1) (hb : d80104 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71208, d80104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71208, d80104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16651 (p : Pattern) (ha : d71211 p = 1) (hb : d80107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53056 q = 1) (hb : d80095 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71201 q = 1) (hb : d80096 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71201, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71201, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d71202 q = 1) (hb : d80097 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71202, d80097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71202, d80097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d71211 q = 1) (hb : d80107 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71211, d80107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71211, d80107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro16652 (p : Pattern) (ha : d71216 p = 1) (hb : d80113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71203 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71203 q = 1) (hb : d80099 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16649 q ha hb
    | true =>
      simp only [d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d71204 q = 1) (hb : d80100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71204, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71204, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71205 q = 1) (hb : d80101 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71205, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71205, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71206 q = 1) (hb : d80102 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71206, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71206, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71207 q = 1) (hb : d80103 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71207, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71207, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d71211 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d71211 q = 1) (hb : d80108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16651 q ha hb
    | true =>
      simp only [d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d71212 q = 1) (hb : d80109 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71212, d80109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71212, d80109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71213 q = 1) (hb : d80110 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71213, d80110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71213, d80110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d71214 q = 1) (hb : d80111 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71214, d80111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71214, d80111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d71215 q = 1) (hb : d80112 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71215, d80112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71215, d80112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d71216 q = 1) (hb : d80113 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71216, d80113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71216, d80113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16653 (p : Pattern) (ha : d71221 p = 1) (hb : d80118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53056 q = 1) (hb : d80095 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71201 q = 1) (hb : d80096 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71201, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71201, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71220 q = 1) (hb : d80117 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71220, d80117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71220, d80117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71221 q = 1) (hb : d80118 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71221, d80118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71221, d80118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16654 (p : Pattern) (ha : d71227 p = 1) (hb : d80125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53056 q = 1) (hb : d80095 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71225 q = 1) (hb : d80123 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71225, d80123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71225, d80123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71226 q = 1) (hb : d80124 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71226, d80124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71226, d80124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d71227 q = 1) (hb : d80125 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71227, d80125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71227, d80125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16655 (p : Pattern) (ha : d80132 p = 1) (hb : d109855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69234 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7883 q = 1) (hb : d69233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d69233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15494 q ha hb
    | true =>
      simp only [d7883, d69233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7884 q = 1) (hb : d69234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d69234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7884, d69234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69234 q = 1) (hb : d80129 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d80130 q = 1) (hb : d109853 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d80130, d109853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d80130, d109853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80131 q = 1) (hb : d109854 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d80131, d109854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80131, d109854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d80132 q = 1) (hb : d109855 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d80132, d109855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80132, d109855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16656 (p : Pattern) (ha : d109860 p = 1) (hb : d110162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71221 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71221 q = 1) (hb : d80119 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16653 q ha hb
    | true =>
      simp only [d80119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d71222 q = 1) (hb : d80120 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71222, d80120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71222, d80120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71223 q = 1) (hb : d80121 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71223, d80121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71223, d80121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71224 q = 1) (hb : d80122 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71224, d80122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71224, d80122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71227 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71227 q = 1) (hb : d80126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16654 q ha hb
    | true =>
      simp only [d80126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d71228 q = 1) (hb : d80127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71228, d80127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71228, d80127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71229 q = 1) (hb : d80128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71229, d80128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71229, d80128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d109855 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d80133 q = 1) (hb : d109855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16655 q ha hb
    | true =>
      simp only [d80133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71203 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d80134 q = 1) (hb : d109856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80134, d109856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80134, d109856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109857 q = 1) (hb : d110159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109857, d110159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d109857, d110159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d109858 q = 1) (hb : d110160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109858, d110160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109858, d110160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109859 q = 1) (hb : d110161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109859, d110161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109859, d110161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109860 q = 1) (hb : d110162 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109860, d110162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109860, d110162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16657 (p : Pattern) (ha : d71239 p = 1) (hb : d80140 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53056 q = 1) (hb : d80095 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71201 q = 1) (hb : d80096 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71201, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71201, d80096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71220 q = 1) (hb : d80117 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71220, d80117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71220, d80117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71239 q = 1) (hb : d80140 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71239, d80140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71239, d80140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro16658 (p : Pattern) (ha : d71243 p = 1) (hb : d80145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1614 q = 1) (hb : d53055 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro215 q ha hb
    | true =>
      simp only [d1614, d53055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1615 q = 1) (hb : d53056 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d53056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53056 q = 1) (hb : d80095 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71225 q = 1) (hb : d80123 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71225, d80123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71225, d80123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71226 q = 1) (hb : d80124 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71226, d80124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71226, d80124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d71243 q = 1) (hb : d80145 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71243, d80145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71243, d80145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro16659 (p : Pattern) (ha : d80149 p = 1) (hb : d109861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69234 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7883 q = 1) (hb : d69233 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7883, d69233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15494 q ha hb
    | true =>
      simp only [d7883, d69233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7884 q = 1) (hb : d69234 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7884, d69234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7884, d69234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69234 q = 1) (hb : d80129 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d80130 q = 1) (hb : d109853 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d80130, d109853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d80130, d109853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d80131 q = 1) (hb : d109854 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d80131, d109854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80131, d109854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d80149 q = 1) (hb : d109861 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d80149, d109861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80149, d109861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro16660 (p : Pattern) (ha : d109866 p = 1) (hb : d110166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71221 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71221 q = 1) (hb : d80119 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16653 q ha hb
    | true =>
      simp only [d80119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d71222 q = 1) (hb : d80120 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71222, d80120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71222, d80120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71223 q = 1) (hb : d80121 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71223, d80121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71223, d80121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71224 q = 1) (hb : d80122 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71224, d80122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71224, d80122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71227 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71227 q = 1) (hb : d80126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16654 q ha hb
    | true =>
      simp only [d80126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d71228 q = 1) (hb : d80127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71228, d80127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71228, d80127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71229 q = 1) (hb : d80128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71229, d80128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71229, d80128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d109855 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d80133 q = 1) (hb : d109855 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16655 q ha hb
    | true =>
      simp only [d80133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71203 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d80134 q = 1) (hb : d109856 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80134, d109856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80134, d109856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109857 q = 1) (hb : d110159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109857, d110159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d109857, d110159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d109858 q = 1) (hb : d110160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109858, d110160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109858, d110160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109859 q = 1) (hb : d110161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109859, d110161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109859, d110161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d71239 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d71239 q = 1) (hb : d80141 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16657 q ha hb
    | true =>
      simp only [d80141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d71240 q = 1) (hb : d80142 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71240, d80142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71240, d80142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d71241 q = 1) (hb : d80143 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71241, d80143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d71241, d80143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d71242 q = 1) (hb : d80144 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71242, d80144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71242, d80144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d71243 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d71243 q = 1) (hb : d80146 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16658 q ha hb
    | true =>
      simp only [d80146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d71244 q = 1) (hb : d80147 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71244, d80147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71244, d80147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d71245 q = 1) (hb : d80148 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71245, d80148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d71245, d80148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d109861 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d80150 q = 1) (hb : d109861 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16659 q ha hb
    | true =>
      simp only [d80150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d71211 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d80151 q = 1) (hb : d109862 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80151, d109862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d80151, d109862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d109863 q = 1) (hb : d110163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109863, d110163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
    | true =>
      simp only [d109863, d110163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d109864 q = 1) (hb : d110164 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109864, d110164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d109864, d110164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d109865 q = 1) (hb : d110165 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109865, d110165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d109865, d110165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d109866 q = 1) (hb : d110166 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109866, d110166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109866, d110166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro16661 (p : Pattern) (ha : d109868 p = 1) (hb : d110168 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71203 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71203 q = 1) (hb : d80099 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16649 q ha hb
    | true =>
      simp only [d80099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d71204 q = 1) (hb : d80100 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71204, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71204, d80100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71205 q = 1) (hb : d80101 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71205, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71205, d80101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71206 q = 1) (hb : d80102 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71206, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71206, d80102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71207 q = 1) (hb : d80103 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71207, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71207, d80103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109868 q = 1) (hb : d110168 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109868, d110168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109868, d110168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro16662 (p : Pattern) (ha : d109875 p = 1) (hb : d110175 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109861 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d80150 q = 1) (hb : d109861 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16659 q ha hb
    | true =>
      simp only [d80150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71211 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d80151 q = 1) (hb : d109862 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80151, d109862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80151, d109862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109863 q = 1) (hb : d110163 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109863, d110163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d109863, d110163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d109873 q = 1) (hb : d110173 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109873, d110173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109873, d110173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109874 q = 1) (hb : d110174 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109874, d110174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109874, d110174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109875 q = 1) (hb : d110175 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109875, d110175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109875, d110175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16663 (p : Pattern) (ha : d80172 p = 1) (hb : d109883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76238 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7989 q = 1) (hb : d76237 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d7989, d76237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15507 q ha hb
    | true =>
      simp only [d7989, d76237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7990 q = 1) (hb : d76238 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d7990, d76238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7990, d76238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76238 q = 1) (hb : d80169 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d80170 q = 1) (hb : d109881 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d80170, d109881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d80170, d109881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d80171 q = 1) (hb : d109882 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d80171, d109882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80171, d109882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d80172 q = 1) (hb : d109883 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d80172, d109883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80172, d109883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro16664 (p : Pattern) (ha : d109888 p = 1) (hb : d110184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109883 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d80173 q = 1) (hb : d109883 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16663 q ha hb
    | true =>
      simp only [d80173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71270 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d80174 q = 1) (hb : d109884 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80174, d109884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80174, d109884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109885 q = 1) (hb : d110181 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109885, d110181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d109885, d110181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d109886 q = 1) (hb : d110182 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109886, d110182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109886, d110182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109887 q = 1) (hb : d110183 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109887, d110183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109887, d110183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109888 q = 1) (hb : d110184 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109888, d110184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109888, d110184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16665 (p : Pattern) (ha : d109894 p = 1) (hb : d110190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71209 q = 1) (hb : d80105 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71209, d80105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71209, d80105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16650 q ha hb
  have h2 (q : Pattern) (ha : d71210 q = 1) (hb : d80106 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71210, d80106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71210, d80106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71217 q = 1) (hb : d80114 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71217, d80114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16650 q ha hb
    | true =>
      simp only [d71217, d80114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16652 q ha hb
  have h4 (q : Pattern) (ha : d71218 q = 1) (hb : d80115 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71218, d80115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71218, d80115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71219 q = 1) (hb : d80116 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71219, d80116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71219, d80116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109867 q = 1) (hb : d110167 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109867, d110167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16656 q ha hb
    | true =>
      simp only [d109867, d110167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16660 q ha hb
  have h7 (q : Pattern) (ha : d109869 q = 1) (hb : d110169 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109869, d110169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16661 q ha hb
    | true =>
      simp only [d109869, d110169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d109870 q = 1) (hb : d110170 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109870, d110170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109870, d110170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109871 q = 1) (hb : d110171 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109871, d110171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d109871, d110171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d109872 q = 1) (hb : d110172 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109872, d110172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109872, d110172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109876 q = 1) (hb : d110176 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109876, d110176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109876, d110176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16662 q ha hb
  have h12 (q : Pattern) (ha : d109877 q = 1) (hb : d110177 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109877, d110177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109877, d110177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d109878 q = 1) (hb : d110178 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109878, d110178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109878, d110178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d109879 q = 1) (hb : d110179 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109879, d110179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109879, d110179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d109880 q = 1) (hb : d110180 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109880, d110180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109880, d110180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109889 q = 1) (hb : d110185 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109889, d110185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109889, d110185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16664 q ha hb
  have h17 (q : Pattern) (ha : d109890 q = 1) (hb : d110186 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109890, d110186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109890, d110186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d109891 q = 1) (hb : d110187 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109891, d110187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109891, d110187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d109892 q = 1) (hb : d110188 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109892, d110188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d109892, d110188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d109893 q = 1) (hb : d110189 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109893, d110189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d109893, d110189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d109894 q = 1) (hb : d110190 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109894, d110190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109894, d110190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro16666 (p : Pattern) (ha : d109900 p = 1) (hb : d110196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109895 q = 1) (hb : d110191 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109895, d110191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109895, d110191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16665 q ha hb
  have h2 (q : Pattern) (ha : d109896 q = 1) (hb : d110192 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109896, d110192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109896, d110192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109897 q = 1) (hb : d110193 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109897, d110193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109897, d110193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109898 q = 1) (hb : d110194 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109898, d110194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109898, d110194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109899 q = 1) (hb : d110195 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109899, d110195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109899, d110195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109900 q = 1) (hb : d110196 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109900, d110196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109900, d110196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16667 (p : Pattern) (ha : d71295 p = 1) (hb : d80204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53377 q = 1) (hb : d80201 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71293 q = 1) (hb : d80202 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71293, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71293, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71294 q = 1) (hb : d80203 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71294, d80203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71294, d80203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d71295 q = 1) (hb : d80204 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71295, d80204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71295, d80204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16668 (p : Pattern) (ha : d71300 p = 1) (hb : d80210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71295 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71295 q = 1) (hb : d80205 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16667 q ha hb
    | true =>
      simp only [d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d71296 q = 1) (hb : d80206 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71296, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71296, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71297 q = 1) (hb : d80207 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71297, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71297, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71298 q = 1) (hb : d80208 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71298, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71298, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71299 q = 1) (hb : d80209 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71299, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71299, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71300 q = 1) (hb : d80210 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71300, d80210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71300, d80210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16669 (p : Pattern) (ha : d71303 p = 1) (hb : d80213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53377 q = 1) (hb : d80201 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71293 q = 1) (hb : d80202 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71293, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71293, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d71294 q = 1) (hb : d80203 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71294, d80203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71294, d80203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d71303 q = 1) (hb : d80213 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71303, d80213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71303, d80213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro16670 (p : Pattern) (ha : d71308 p = 1) (hb : d80219 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71295 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71295 q = 1) (hb : d80205 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16667 q ha hb
    | true =>
      simp only [d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d71296 q = 1) (hb : d80206 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71296, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71296, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71297 q = 1) (hb : d80207 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71297, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71297, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71298 q = 1) (hb : d80208 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71298, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71298, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71299 q = 1) (hb : d80209 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71299, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71299, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d71303 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d71303 q = 1) (hb : d80214 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16669 q ha hb
    | true =>
      simp only [d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d71304 q = 1) (hb : d80215 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71304, d80215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71304, d80215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d71305 q = 1) (hb : d80216 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71305, d80216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d71305, d80216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d71306 q = 1) (hb : d80217 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71306, d80217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71306, d80217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d71307 q = 1) (hb : d80218 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71307, d80218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71307, d80218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d71308 q = 1) (hb : d80219 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d71308, d80219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71308, d80219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16671 (p : Pattern) (ha : d71313 p = 1) (hb : d80224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53377 q = 1) (hb : d80201 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71293 q = 1) (hb : d80202 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71293, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71293, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71312 q = 1) (hb : d80223 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71312, d80223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71312, d80223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71313 q = 1) (hb : d80224 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71313, d80224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71313, d80224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16672 (p : Pattern) (ha : d71319 p = 1) (hb : d80231 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53377 q = 1) (hb : d80201 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71317 q = 1) (hb : d80229 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71317, d80229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71317, d80229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71318 q = 1) (hb : d80230 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71318, d80230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71318, d80230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d71319 q = 1) (hb : d80231 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71319, d80231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71319, d80231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16673 (p : Pattern) (ha : d80238 p = 1) (hb : d109907 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69344 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8038 q = 1) (hb : d69343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d69343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15518 q ha hb
    | true =>
      simp only [d8038, d69343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8039 q = 1) (hb : d69344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d69344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8039, d69344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69344 q = 1) (hb : d80235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d80236 q = 1) (hb : d109905 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d80236, d109905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d80236, d109905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80237 q = 1) (hb : d109906 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d80237, d109906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80237, d109906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d80238 q = 1) (hb : d109907 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d80238, d109907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80238, d109907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16674 (p : Pattern) (ha : d109912 p = 1) (hb : d110204 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71313 q = 1) (hb : d80225 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16671 q ha hb
    | true =>
      simp only [d80225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d71314 q = 1) (hb : d80226 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71314, d80226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71314, d80226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71315 q = 1) (hb : d80227 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71315, d80227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71315, d80227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71316 q = 1) (hb : d80228 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71316, d80228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71316, d80228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71319 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71319 q = 1) (hb : d80232 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16672 q ha hb
    | true =>
      simp only [d80232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d71320 q = 1) (hb : d80233 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71320, d80233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71320, d80233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71321 q = 1) (hb : d80234 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71321, d80234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71321, d80234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d109907 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d80239 q = 1) (hb : d109907 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16673 q ha hb
    | true =>
      simp only [d80239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71295 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d80240 q = 1) (hb : d109908 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80240, d109908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80240, d109908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109909 q = 1) (hb : d110201 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109909, d110201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d109909, d110201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d109910 q = 1) (hb : d110202 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109910, d110202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109910, d110202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109911 q = 1) (hb : d110203 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109911, d110203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109911, d110203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d109912 q = 1) (hb : d110204 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109912, d110204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109912, d110204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16675 (p : Pattern) (ha : d71331 p = 1) (hb : d80246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53377 q = 1) (hb : d80201 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71293 q = 1) (hb : d80202 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71293, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71293, d80202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d71312 q = 1) (hb : d80223 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71312, d80223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71312, d80223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d71331 q = 1) (hb : d80246 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71331, d80246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71331, d80246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro16676 (p : Pattern) (ha : d71335 p = 1) (hb : d80251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2097 q = 1) (hb : d53376 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro274 q ha hb
    | true =>
      simp only [d2097, d53376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2098 q = 1) (hb : d53377 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d53377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53377 q = 1) (hb : d80201 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d80201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71317 q = 1) (hb : d80229 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71317, d80229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71317, d80229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71318 q = 1) (hb : d80230 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71318, d80230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71318, d80230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d71335 q = 1) (hb : d80251 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71335, d80251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71335, d80251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro16677 (p : Pattern) (ha : d80255 p = 1) (hb : d109913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d69344 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8038 q = 1) (hb : d69343 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8038, d69343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15518 q ha hb
    | true =>
      simp only [d8038, d69343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8039 q = 1) (hb : d69344 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8039, d69344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8039, d69344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69344 q = 1) (hb : d80235 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d80236 q = 1) (hb : d109905 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d80236, d109905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d80236, d109905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d80237 q = 1) (hb : d109906 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d80237, d109906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80237, d109906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d80255 q = 1) (hb : d109913 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d80255, d109913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80255, d109913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro16678 (p : Pattern) (ha : d109918 p = 1) (hb : d110208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71313 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71313 q = 1) (hb : d80225 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16671 q ha hb
    | true =>
      simp only [d80225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d71314 q = 1) (hb : d80226 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71314, d80226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71314, d80226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71315 q = 1) (hb : d80227 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71315, d80227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71315, d80227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71316 q = 1) (hb : d80228 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71316, d80228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71316, d80228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d71319 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d71319 q = 1) (hb : d80232 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16672 q ha hb
    | true =>
      simp only [d80232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d71320 q = 1) (hb : d80233 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71320, d80233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71320, d80233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d71321 q = 1) (hb : d80234 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71321, d80234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d71321, d80234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d109907 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d80239 q = 1) (hb : d109907 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16673 q ha hb
    | true =>
      simp only [d80239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d71295 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d80240 q = 1) (hb : d109908 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80240, d109908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80240, d109908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109909 q = 1) (hb : d110201 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109909, d110201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d109909, d110201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d109910 q = 1) (hb : d110202 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109910, d110202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109910, d110202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109911 q = 1) (hb : d110203 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109911, d110203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109911, d110203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d0 q = 1) (hb : d71331 q = 1) : d0 q = 1 := by
    exact ha
  have h18 (q : Pattern) (ha : d71331 q = 1) (hb : d80247 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16675 q ha hb
    | true =>
      simp only [d80247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q hb ha
  have h19 (q : Pattern) (ha : d71332 q = 1) (hb : d80248 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71332, d80248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71332, d80248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d71333 q = 1) (hb : d80249 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71333, d80249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d71333, d80249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d71334 q = 1) (hb : d80250 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71334, d80250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71334, d80250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d71335 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d71335 q = 1) (hb : d80252 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16676 q ha hb
    | true =>
      simp only [d80252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d71336 q = 1) (hb : d80253 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71336, d80253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71336, d80253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d71337 q = 1) (hb : d80254 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71337, d80254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d71337, d80254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h26 (q : Pattern) (ha : d0 q = 1) (hb : d109913 q = 1) : d0 q = 1 := by
    exact ha
  have h27 (q : Pattern) (ha : d80256 q = 1) (hb : d109913 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16677 q ha hb
    | true =>
      simp only [d80256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d71303 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d80257 q = 1) (hb : d109914 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80257, d109914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d80257, d109914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d109915 q = 1) (hb : d110205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109915, d110205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
    | true =>
      simp only [d109915, d110205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d109916 q = 1) (hb : d110206 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109916, d110206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d109916, d110206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d109917 q = 1) (hb : d110207 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109917, d110207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d109917, d110207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  have h33 (q : Pattern) (ha : d109918 q = 1) (hb : d110208 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109918, d110208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109918, d110208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q ha hb
  exact h33 p ha hb
theorem andIntro16679 (p : Pattern) (ha : d109920 p = 1) (hb : d110210 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71295 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d71295 q = 1) (hb : d80205 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16667 q ha hb
    | true =>
      simp only [d80205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d71296 q = 1) (hb : d80206 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d71296, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71296, d80206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d71297 q = 1) (hb : d80207 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d71297, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71297, d80207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71298 q = 1) (hb : d80208 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d71298, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71298, d80208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d71299 q = 1) (hb : d80209 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d71299, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71299, d80209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109920 q = 1) (hb : d110210 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109920, d110210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109920, d110210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro16680 (p : Pattern) (ha : d109927 p = 1) (hb : d110217 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109913 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d80256 q = 1) (hb : d109913 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16677 q ha hb
    | true =>
      simp only [d80256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71303 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d80257 q = 1) (hb : d109914 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80257, d109914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80257, d109914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109915 q = 1) (hb : d110205 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109915, d110205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d109915, d110205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d109925 q = 1) (hb : d110215 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109925, d110215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109925, d110215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109926 q = 1) (hb : d110216 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109926, d110216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109926, d110216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109927 q = 1) (hb : d110217 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109927, d110217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109927, d110217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16681 (p : Pattern) (ha : d80278 p = 1) (hb : d109935 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d76374 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8144 q = 1) (hb : d76373 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d8144, d76373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15531 q ha hb
    | true =>
      simp only [d8144, d76373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8145 q = 1) (hb : d76374 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d8145, d76374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8145, d76374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d76374 q = 1) (hb : d80275 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d80275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d80275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d80276 q = 1) (hb : d109933 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d80276, d109933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d80276, d109933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d80277 q = 1) (hb : d109934 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d80277, d109934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d80277, d109934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d80278 q = 1) (hb : d109935 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d80278, d109935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80278, d109935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro16682 (p : Pattern) (ha : d109940 p = 1) (hb : d110226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109935 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d80279 q = 1) (hb : d109935 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d80279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16681 q ha hb
    | true =>
      simp only [d80279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71362 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d80280 q = 1) (hb : d109936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80280, d109936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d80280, d109936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109937 q = 1) (hb : d110223 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109937, d110223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d109937, d110223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d109938 q = 1) (hb : d110224 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109938, d110224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109938, d110224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109939 q = 1) (hb : d110225 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109939, d110225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109939, d110225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109940 q = 1) (hb : d110226 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109940, d110226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109940, d110226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16683 (p : Pattern) (ha : d109946 p = 1) (hb : d110232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d71301 q = 1) (hb : d80211 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71301, d80211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d71301, d80211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16668 q ha hb
  have h2 (q : Pattern) (ha : d71302 q = 1) (hb : d80212 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71302, d80212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d71302, d80212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d71309 q = 1) (hb : d80220 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d71309, d80220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16668 q ha hb
    | true =>
      simp only [d71309, d80220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16670 q ha hb
  have h4 (q : Pattern) (ha : d71310 q = 1) (hb : d80221 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d71310, d80221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d71310, d80221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d71311 q = 1) (hb : d80222 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d71311, d80222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d71311, d80222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109919 q = 1) (hb : d110209 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109919, d110209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16674 q ha hb
    | true =>
      simp only [d109919, d110209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16678 q ha hb
  have h7 (q : Pattern) (ha : d109921 q = 1) (hb : d110211 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109921, d110211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16679 q ha hb
    | true =>
      simp only [d109921, d110211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d109922 q = 1) (hb : d110212 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109922, d110212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109922, d110212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109923 q = 1) (hb : d110213 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109923, d110213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d109923, d110213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d109924 q = 1) (hb : d110214 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109924, d110214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109924, d110214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109928 q = 1) (hb : d110218 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109928, d110218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109928, d110218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16680 q ha hb
  have h12 (q : Pattern) (ha : d109929 q = 1) (hb : d110219 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109929, d110219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109929, d110219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d109930 q = 1) (hb : d110220 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109930, d110220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109930, d110220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d109931 q = 1) (hb : d110221 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109931, d110221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109931, d110221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d109932 q = 1) (hb : d110222 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109932, d110222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109932, d110222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109941 q = 1) (hb : d110227 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109941, d110227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109941, d110227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16682 q ha hb
  have h17 (q : Pattern) (ha : d109942 q = 1) (hb : d110228 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109942, d110228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109942, d110228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d109943 q = 1) (hb : d110229 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109943, d110229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109943, d110229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d109944 q = 1) (hb : d110230 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109944, d110230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d109944, d110230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d109945 q = 1) (hb : d110231 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109945, d110231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d109945, d110231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d109946 q = 1) (hb : d110232 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109946, d110232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109946, d110232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro16684 (p : Pattern) (ha : d109952 p = 1) (hb : d110238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109947 q = 1) (hb : d110233 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109947, d110233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109947, d110233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16683 q ha hb
  have h2 (q : Pattern) (ha : d109948 q = 1) (hb : d110234 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109948, d110234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109948, d110234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109949 q = 1) (hb : d110235 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109949, d110235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109949, d110235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109950 q = 1) (hb : d110236 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109950, d110236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109950, d110236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109951 q = 1) (hb : d110237 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109951, d110237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109951, d110237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109952 q = 1) (hb : d110238 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109952, d110238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109952, d110238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16685 (p : Pattern) (ha : d109958 p = 1) (hb : d110244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d109751 q = 1) (hb : d110077 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109751, d110077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16594 q ha hb
    | true =>
      simp only [d109751, d110077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16612 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d109800 q = 1) (hb : d110116 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109800, d110116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109800, d110116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16630 q ha hb
  have h3 (q : Pattern) (ha : d109801 q = 1) (hb : d110117 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109801, d110117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109801, d110117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109850 q = 1) (hb : d110156 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109850, d110156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109850, d110156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16648 q ha hb
  have h5 (q : Pattern) (ha : d109851 q = 1) (hb : d110157 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109851, d110157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109851, d110157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109852 q = 1) (hb : d110158 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109852, d110158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109852, d110158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109901 q = 1) (hb : d110197 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109901, d110197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109901, d110197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16666 q ha hb
  have h8 (q : Pattern) (ha : d109902 q = 1) (hb : d110198 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109902, d110198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109902, d110198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109903 q = 1) (hb : d110199 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109903, d110199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109903, d110199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109904 q = 1) (hb : d110200 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109904, d110200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109904, d110200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109953 q = 1) (hb : d110239 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109953, d110239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109953, d110239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16684 q ha hb
  have h12 (q : Pattern) (ha : d109954 q = 1) (hb : d110240 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109954, d110240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109954, d110240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109955 q = 1) (hb : d110241 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109955, d110241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109955, d110241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109956 q = 1) (hb : d110242 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109956, d110242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109956, d110242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d109957 q = 1) (hb : d110243 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d109957, d110243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109957, d110243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109958 q = 1) (hb : d110244 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d109958, d110244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109958, d110244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro16686 (p : Pattern) (ha : d109964 p = 1) (hb : d110250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109959 q = 1) (hb : d110245 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d109959, d110245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16685 q ha hb
    | true =>
      simp only [d109959, d110245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d109960 q = 1) (hb : d110246 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d109960, d110246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109960, d110246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d109961 q = 1) (hb : d110247 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d109961, d110247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109961, d110247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d109962 q = 1) (hb : d110248 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d109962, d110248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109962, d110248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d109963 q = 1) (hb : d110249 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d109963, d110249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109963, d110249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d109964 q = 1) (hb : d110250 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d109964, d110250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109964, d110250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16687 (p : Pattern) (ha : d109970 p = 1) (hb : d110256 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109965 q = 1) (hb : d110251 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d109965, d110251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16686 q ha hb
    | true =>
      simp only [d109965, d110251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d109966 q = 1) (hb : d110252 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d109966, d110252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109966, d110252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d109967 q = 1) (hb : d110253 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d109967, d110253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109967, d110253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d109968 q = 1) (hb : d110254 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d109968, d110254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109968, d110254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d109969 q = 1) (hb : d110255 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d109969, d110255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109969, d110255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d109970 q = 1) (hb : d110256 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d109970, d110256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109970, d110256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16688 (p : Pattern) (ha : d109976 p = 1) (hb : d110262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109971 q = 1) (hb : d110257 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d109971, d110257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16687 q ha hb
    | true =>
      simp only [d109971, d110257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d109972 q = 1) (hb : d110258 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d109972, d110258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109972, d110258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d109973 q = 1) (hb : d110259 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d109973, d110259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109973, d110259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d109974 q = 1) (hb : d110260 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d109974, d110260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109974, d110260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d109975 q = 1) (hb : d110261 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d109975, d110261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109975, d110261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d109976 q = 1) (hb : d110262 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d109976, d110262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109976, d110262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16689 (p : Pattern) (ha : d109982 p = 1) (hb : d110268 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109977 q = 1) (hb : d110263 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d109977, d110263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16688 q ha hb
    | true =>
      simp only [d109977, d110263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d109978 q = 1) (hb : d110264 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d109978, d110264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109978, d110264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d109979 q = 1) (hb : d110265 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d109979, d110265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109979, d110265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d109980 q = 1) (hb : d110266 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d109980, d110266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109980, d110266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d109981 q = 1) (hb : d110267 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d109981, d110267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109981, d110267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d109982 q = 1) (hb : d110268 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d109982, d110268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109982, d110268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16690 (p : Pattern) (ha : d109988 p = 1) (hb : d110274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109983 q = 1) (hb : d110269 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d109983, d110269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16689 q ha hb
    | true =>
      simp only [d109983, d110269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d109984 q = 1) (hb : d110270 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d109984, d110270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109984, d110270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d109985 q = 1) (hb : d110271 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d109985, d110271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109985, d110271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d109986 q = 1) (hb : d110272 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d109986, d110272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109986, d110272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d109987 q = 1) (hb : d110273 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d109987, d110273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109987, d110273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d109988 q = 1) (hb : d110274 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d109988, d110274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109988, d110274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16691 (p : Pattern) (ha : d109994 p = 1) (hb : d110280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109989 q = 1) (hb : d110275 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d109989, d110275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16690 q ha hb
    | true =>
      simp only [d109989, d110275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d109990 q = 1) (hb : d110276 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d109990, d110276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109990, d110276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d109991 q = 1) (hb : d110277 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d109991, d110277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109991, d110277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d109992 q = 1) (hb : d110278 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d109992, d110278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109992, d110278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d109993 q = 1) (hb : d110279 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d109993, d110279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109993, d110279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d109994 q = 1) (hb : d110280 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d109994, d110280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109994, d110280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16692 (p : Pattern) (ha : d110000 p = 1) (hb : d110286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109995 q = 1) (hb : d110281 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d109995, d110281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16691 q ha hb
    | true =>
      simp only [d109995, d110281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d109996 q = 1) (hb : d110282 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d109996, d110282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109996, d110282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d109997 q = 1) (hb : d110283 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d109997, d110283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109997, d110283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d109998 q = 1) (hb : d110284 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d109998, d110284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109998, d110284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d109999 q = 1) (hb : d110285 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d109999, d110285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109999, d110285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d110000 q = 1) (hb : d110286 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d110000, d110286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d110000, d110286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16693 (p : Pattern) (ha : d77845 p = 1) (hb : d99199 p = 1) : d80353 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d49 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7255 q = 1) (hb : d77845 q = 1) : d79659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d77845, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16433 q ha hb
    | true =>
      simp only [d7255, d77845, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7305 q = 1) (hb : d77845 q = 1) : d79703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7305, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7305, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7306 q = 1) (hb : d77845 q = 1) : d79704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7306, d79704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7306, d79704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7307 q = 1) (hb : d77845 q = 1) : d79705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7307, d79705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7307, d79705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7308 q = 1) (hb : d77845 q = 1) : d79706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7308, d79706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7308, d79706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d99199 q = 1) : d80353 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99199, d80353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99199, d80353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro16694 (p : Pattern) (ha : d77845 p = 1) (hb : d99209 p = 1) : d80363 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7281 q = 1) (hb : d77845 q = 1) : d79679 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7281, d77845, d79679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16436 q ha hb
    | true =>
      simp only [d7281, d77845, d79679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99205 q = 1) : d80359 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99205, d80359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99205, d80359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99206 q = 1) : d80360 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99206, d80360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99206, d80360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99207 q = 1) : d80361 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99207, d80361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99207, d80361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99208 q = 1) : d80362 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99208, d80362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99208, d80362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d99209 q = 1) : d80363 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99209, d80363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99209, d80363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16695 (p : Pattern) (ha : d77845 p = 1) (hb : d99215 p = 1) : d80369 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7310 q = 1) (hb : d77845 q = 1) : d79708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7310, d79708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16439 q ha hb
    | true =>
      simp only [d7310, d79708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16440 q ha hb
  have h2 (q : Pattern) (ha : d7311 q = 1) (hb : d77845 q = 1) : d79709 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7311, d79709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7311, d79709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99197 q = 1) : d80351 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99197, d80351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d99197, d80351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99198 q = 1) : d80352 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99198, d80352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99198, d80352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99200 q = 1) : d80354 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99200, d80354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99200, d80354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16693 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99201 q = 1) : d80355 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99201, d80355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99201, d80355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d99202 q = 1) : d80356 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99202, d80356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99202, d80356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d99203 q = 1) : d80357 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99203, d80357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99203, d80357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d99204 q = 1) : d80358 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99204, d80358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99204, d80358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d99210 q = 1) : d80364 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99210, d80364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99210, d80364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16694 q ha hb
  have h11 (q : Pattern) (ha : d77845 q = 1) (hb : d99211 q = 1) : d80365 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99211, d80365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99211, d80365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d99212 q = 1) : d80366 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99212, d80366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99212, d80366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d77845 q = 1) (hb : d99213 q = 1) : d80367 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99213, d80367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99213, d80367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d77845 q = 1) (hb : d99214 q = 1) : d80368 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99214, d80368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99214, d80368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d77845 q = 1) (hb : d99215 q = 1) : d80369 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99215, d80369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99215, d80369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16696 (p : Pattern) (ha : d77845 p = 1) (hb : d99221 p = 1) : d80375 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8470 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99216 q = 1) : d80370 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99216, d80370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99216, d80370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16695 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d99217 q = 1) : d80371 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99217, d80371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99217, d80371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d99218 q = 1) : d80372 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99218, d80372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99218, d80372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d99219 q = 1) : d80373 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99219, d80373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99219, d80373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d99220 q = 1) : d80374 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99220, d80374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99220, d80374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77845 q = 1) (hb : d99221 q = 1) : d80375 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99221, d80375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d99221, d80375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro16697 (p : Pattern) (ha : d77845 p = 1) (hb : d99224 p = 1) : d80378 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d501 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7443 q = 1) (hb : d77845 q = 1) : d79796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7443, d77845, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16460 q ha hb
    | true =>
      simp only [d7443, d77845, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7444 q = 1) (hb : d77845 q = 1) : d79797 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7444, d79797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7444, d79797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7445 q = 1) (hb : d77845 q = 1) : d79798 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7445, d79798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7445, d79798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7446 q = 1) (hb : d77845 q = 1) : d79799 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7446, d79799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7446, d79799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7447 q = 1) (hb : d77845 q = 1) : d79800 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7447, d79800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7447, d79800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d99224 q = 1) : d80378 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99224, d80378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99224, d80378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro16698 (p : Pattern) (ha : d7539 p = 1) (hb : d77844 p = 1) : d79866 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7392 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d685 q = 1) (hb : d77842 q = 1) : d685 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7536 q = 1) (hb : d77844 q = 1) : d79863 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7536, d77844, d79863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7536, d77844, d79863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7537 q = 1) (hb : d77844 q = 1) : d79864 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7537, d79864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7537, d79864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7538 q = 1) (hb : d77844 q = 1) : d79865 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7538, d79865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7538, d79865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7539 q = 1) (hb : d77844 q = 1) : d79866 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7539, d79866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7539, d79866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16699 (p : Pattern) (ha : d77845 p = 1) (hb : d99235 p = 1) : d80388 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d730 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d99230 q = 1) : d79867 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77845, d99230, d79867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16698 q hb ha
    | true =>
      simp only [d77845, d99230, d79867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99231 q = 1) : d80384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99231, d80384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99231, d80384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99232 q = 1) : d80385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99232, d80385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99232, d80385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99233 q = 1) : d80386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99233, d80386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99233, d80386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99234 q = 1) : d80387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99234, d80387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99234, d80387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d99235 q = 1) : d80388 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99235, d80388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99235, d80388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16700 (p : Pattern) (ha : d77845 p = 1) (hb : d99241 p = 1) : d80394 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7449 q = 1) (hb : d77845 q = 1) : d79802 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7449, d79802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16459 q ha hb
    | true =>
      simp only [d7449, d79802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16461 q ha hb
  have h2 (q : Pattern) (ha : d7450 q = 1) (hb : d77845 q = 1) : d79803 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7450, d79803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7450, d79803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99222 q = 1) : d80376 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99222, d80376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d99222, d80376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99223 q = 1) : d80377 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99223, d80377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99223, d80377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99225 q = 1) : d80379 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99225, d80379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99225, d80379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16697 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99226 q = 1) : d80380 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99226, d80380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99226, d80380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d99227 q = 1) : d80381 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99227, d80381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99227, d80381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d99228 q = 1) : d80382 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99228, d80382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99228, d80382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d99229 q = 1) : d80383 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99229, d80383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99229, d80383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d99236 q = 1) : d80389 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99236, d80389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99236, d80389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16699 q ha hb
  have h11 (q : Pattern) (ha : d77845 q = 1) (hb : d99237 q = 1) : d80390 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99237, d80390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99237, d80390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d99238 q = 1) : d80391 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99238, d80391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99238, d80391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d77845 q = 1) (hb : d99239 q = 1) : d80392 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99239, d80392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99239, d80392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d77845 q = 1) (hb : d99240 q = 1) : d80393 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99240, d80393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99240, d80393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d77845 q = 1) (hb : d99241 q = 1) : d80394 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99241, d80394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99241, d80394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16701 (p : Pattern) (ha : d77845 p = 1) (hb : d99247 p = 1) : d80400 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d99242 q = 1) : d80395 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99242, d80395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99242, d80395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16700 q ha hb
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d99243 q = 1) : d80396 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99243, d80396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99243, d80396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99244 q = 1) : d80397 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99244, d80397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99244, d80397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99245 q = 1) : d80398 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99245, d80398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99245, d80398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99246 q = 1) : d80399 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99246, d80399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99246, d80399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99247 q = 1) : d80400 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99247, d80400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99247, d80400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16702 (p : Pattern) (ha : d77845 p = 1) (hb : d99251 p = 1) : d80404 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d793 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7591 q = 1) (hb : d77845 q = 1) : d79899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7591, d77845, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16481 q ha hb
    | true =>
      simp only [d7591, d77845, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7592 q = 1) (hb : d77845 q = 1) : d79900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, d79900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7592, d79900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7593 q = 1) (hb : d77845 q = 1) : d79901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, d79901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7593, d79901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7594 q = 1) (hb : d77845 q = 1) : d79902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, d79902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7594, d79902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7595 q = 1) (hb : d77845 q = 1) : d79903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, d79903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7595, d79903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d99251 q = 1) : d80404 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99251, d80404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99251, d80404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro16703 (p : Pattern) (ha : d7691 p = 1) (hb : d77844 p = 1) : d79969 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7683 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1007 q = 1) (hb : d77842 q = 1) : d1007 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7688 q = 1) (hb : d77844 q = 1) : d79966 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7688, d77844, d79966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7688, d77844, d79966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7689 q = 1) (hb : d77844 q = 1) : d79967 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7689, d79967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7689, d79967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7690 q = 1) (hb : d77844 q = 1) : d79968 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7690, d79968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7690, d79968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7691 q = 1) (hb : d77844 q = 1) : d79969 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7691, d79969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7691, d79969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16704 (p : Pattern) (ha : d77845 p = 1) (hb : d99262 p = 1) : d80414 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1063 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d99257 q = 1) : d79970 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77845, d99257, d79970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16703 q hb ha
    | true =>
      simp only [d77845, d99257, d79970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99258 q = 1) : d80410 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99258, d80410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99258, d80410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99259 q = 1) : d80411 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99259, d80411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99259, d80411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99260 q = 1) : d80412 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99260, d80412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99260, d80412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99261 q = 1) : d80413 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99261, d80413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99261, d80413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d99262 q = 1) : d80414 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99262, d80414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99262, d80414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16705 (p : Pattern) (ha : d77845 p = 1) (hb : d99268 p = 1) : d80420 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7597 q = 1) (hb : d77845 q = 1) : d79905 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7597, d79905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16480 q ha hb
    | true =>
      simp only [d7597, d79905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16482 q ha hb
  have h2 (q : Pattern) (ha : d7598 q = 1) (hb : d77845 q = 1) : d79906 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7598, d79906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7598, d79906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99249 q = 1) : d80402 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99249, d80402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d99249, d80402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99250 q = 1) : d80403 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99250, d80403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99250, d80403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99252 q = 1) : d80405 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99252, d80405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99252, d80405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16702 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99253 q = 1) : d80406 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99253, d80406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99253, d80406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d99254 q = 1) : d80407 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99254, d80407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99254, d80407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d99255 q = 1) : d80408 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99255, d80408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99255, d80408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d99256 q = 1) : d80409 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99256, d80409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99256, d80409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d99263 q = 1) : d80415 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99263, d80415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99263, d80415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16704 q ha hb
  have h11 (q : Pattern) (ha : d77845 q = 1) (hb : d99264 q = 1) : d80416 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99264, d80416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99264, d80416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d99265 q = 1) : d80417 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99265, d80417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99265, d80417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d77845 q = 1) (hb : d99266 q = 1) : d80418 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99266, d80418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99266, d80418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d77845 q = 1) (hb : d99267 q = 1) : d80419 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99267, d80419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99267, d80419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d77845 q = 1) (hb : d99268 q = 1) : d80420 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99268, d80420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99268, d80420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16706 (p : Pattern) (ha : d77845 p = 1) (hb : d99274 p = 1) : d80426 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d99269 q = 1) : d80421 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99269, d80421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99269, d80421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16705 q ha hb
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d99270 q = 1) : d80422 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99270, d80422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99270, d80422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99271 q = 1) : d80423 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99271, d80423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99271, d80423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99272 q = 1) : d80424 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99272, d80424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99272, d80424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99273 q = 1) : d80425 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99273, d80425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99273, d80425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99274 q = 1) : d80426 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99274, d80426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99274, d80426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16707 (p : Pattern) (ha : d77845 p = 1) (hb : d99279 p = 1) : d80431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1172 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7744 q = 1) (hb : d77845 q = 1) : d80003 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7744, d77845, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16502 q ha hb
    | true =>
      simp only [d7744, d77845, d80003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7745 q = 1) (hb : d77845 q = 1) : d80004 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, d80004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7745, d80004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7746 q = 1) (hb : d77845 q = 1) : d80005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, d80005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7746, d80005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7747 q = 1) (hb : d77845 q = 1) : d80006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, d80006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7747, d80006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7748 q = 1) (hb : d77845 q = 1) : d80007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, d80007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7748, d80007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d99279 q = 1) : d80431 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99279, d80431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99279, d80431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro16708 (p : Pattern) (ha : d7844 p = 1) (hb : d77844 p = 1) : d80073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7836 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1432 q = 1) (hb : d77842 q = 1) : d1432 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7841 q = 1) (hb : d77844 q = 1) : d80070 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7841, d77844, d80070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7841, d77844, d80070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7842 q = 1) (hb : d77844 q = 1) : d80071 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7842, d80071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7842, d80071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7843 q = 1) (hb : d77844 q = 1) : d80072 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7843, d80072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7843, d80072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7844 q = 1) (hb : d77844 q = 1) : d80073 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7844, d80073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7844, d80073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16709 (p : Pattern) (ha : d77845 p = 1) (hb : d99290 p = 1) : d80441 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1497 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d99285 q = 1) : d80074 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77845, d99285, d80074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16708 q hb ha
    | true =>
      simp only [d77845, d99285, d80074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99286 q = 1) : d80437 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99286, d80437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99286, d80437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99287 q = 1) : d80438 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99287, d80438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99287, d80438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99288 q = 1) : d80439 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99288, d80439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99288, d80439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99289 q = 1) : d80440 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99289, d80440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99289, d80440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d99290 q = 1) : d80441 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99290, d80441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99290, d80441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16710 (p : Pattern) (ha : d77845 p = 1) (hb : d99296 p = 1) : d80447 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7750 q = 1) (hb : d77845 q = 1) : d80009 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7750, d80009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16501 q ha hb
    | true =>
      simp only [d7750, d80009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16503 q ha hb
  have h2 (q : Pattern) (ha : d7751 q = 1) (hb : d77845 q = 1) : d80010 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7751, d80010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7751, d80010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99277 q = 1) : d80429 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99277, d80429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d99277, d80429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99278 q = 1) : d80430 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99278, d80430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99278, d80430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99280 q = 1) : d80432 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99280, d80432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99280, d80432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16707 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99281 q = 1) : d80433 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99281, d80433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99281, d80433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d99282 q = 1) : d80434 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99282, d80434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99282, d80434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d99283 q = 1) : d80435 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99283, d80435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99283, d80435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d99284 q = 1) : d80436 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99284, d80436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99284, d80436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d99291 q = 1) : d80442 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99291, d80442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99291, d80442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16709 q ha hb
  have h11 (q : Pattern) (ha : d77845 q = 1) (hb : d99292 q = 1) : d80443 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99292, d80443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99292, d80443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d99293 q = 1) : d80444 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99293, d80444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99293, d80444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d77845 q = 1) (hb : d99294 q = 1) : d80445 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99294, d80445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99294, d80445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d77845 q = 1) (hb : d99295 q = 1) : d80446 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99295, d80446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99295, d80446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d77845 q = 1) (hb : d99296 q = 1) : d80447 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99296, d80447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99296, d80447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16711 (p : Pattern) (ha : d77845 p = 1) (hb : d99302 p = 1) : d80453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d99297 q = 1) : d80448 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99297, d80448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99297, d80448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16710 q ha hb
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d99298 q = 1) : d80449 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99298, d80449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99298, d80449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99299 q = 1) : d80450 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99299, d80450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99299, d80450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99300 q = 1) : d80451 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99300, d80451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99300, d80451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99301 q = 1) : d80452 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99301, d80452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99301, d80452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99302 q = 1) : d80453 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99302, d80453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99302, d80453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16712 (p : Pattern) (ha : d77845 p = 1) (hb : d99308 p = 1) : d80459 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1633 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7898 q = 1) (hb : d77845 q = 1) : d80108 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7898, d77845, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16523 q ha hb
    | true =>
      simp only [d7898, d77845, d80108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7899 q = 1) (hb : d77845 q = 1) : d80109 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, d80109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7899, d80109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7900 q = 1) (hb : d77845 q = 1) : d80110 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, d80110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7900, d80110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7901 q = 1) (hb : d77845 q = 1) : d80111 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, d80111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7901, d80111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7902 q = 1) (hb : d77845 q = 1) : d80112 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, d80112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7902, d80112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d99308 q = 1) : d80459 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99308, d80459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99308, d80459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro16713 (p : Pattern) (ha : d7998 p = 1) (hb : d77844 p = 1) : d80178 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7990 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1909 q = 1) (hb : d77842 q = 1) : d1909 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7995 q = 1) (hb : d77844 q = 1) : d80175 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7995, d77844, d80175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7995, d77844, d80175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7996 q = 1) (hb : d77844 q = 1) : d80176 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7996, d80176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7996, d80176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7997 q = 1) (hb : d77844 q = 1) : d80177 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7997, d80177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7997, d80177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7998 q = 1) (hb : d77844 q = 1) : d80178 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7998, d80178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7998, d80178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16714 (p : Pattern) (ha : d77845 p = 1) (hb : d99319 p = 1) : d80469 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1974 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d99314 q = 1) : d80179 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77845, d99314, d80179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16713 q hb ha
    | true =>
      simp only [d77845, d99314, d80179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99315 q = 1) : d80465 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99315, d80465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99315, d80465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99316 q = 1) : d80466 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99316, d80466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99316, d80466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99317 q = 1) : d80467 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99317, d80467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99317, d80467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99318 q = 1) : d80468 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99318, d80468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99318, d80468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d99319 q = 1) : d80469 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99319, d80469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99319, d80469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16715 (p : Pattern) (ha : d77845 p = 1) (hb : d99325 p = 1) : d80475 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7904 q = 1) (hb : d77845 q = 1) : d80114 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7904, d80114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16522 q ha hb
    | true =>
      simp only [d7904, d80114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16524 q ha hb
  have h2 (q : Pattern) (ha : d7905 q = 1) (hb : d77845 q = 1) : d80115 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7905, d80115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7905, d80115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99306 q = 1) : d80457 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99306, d80457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d99306, d80457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99307 q = 1) : d80458 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99307, d80458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99307, d80458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99309 q = 1) : d80460 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99309, d80460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99309, d80460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16712 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99310 q = 1) : d80461 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99310, d80461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99310, d80461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d99311 q = 1) : d80462 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99311, d80462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99311, d80462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d99312 q = 1) : d80463 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99312, d80463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99312, d80463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d99313 q = 1) : d80464 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99313, d80464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99313, d80464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d99320 q = 1) : d80470 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99320, d80470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99320, d80470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16714 q ha hb
  have h11 (q : Pattern) (ha : d77845 q = 1) (hb : d99321 q = 1) : d80471 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99321, d80471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99321, d80471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d99322 q = 1) : d80472 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99322, d80472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99322, d80472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d77845 q = 1) (hb : d99323 q = 1) : d80473 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99323, d80473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99323, d80473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d77845 q = 1) (hb : d99324 q = 1) : d80474 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99324, d80474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99324, d80474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d77845 q = 1) (hb : d99325 q = 1) : d80475 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99325, d80475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99325, d80475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16716 (p : Pattern) (ha : d77845 p = 1) (hb : d99331 p = 1) : d80481 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d99326 q = 1) : d80476 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99326, d80476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99326, d80476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16715 q ha hb
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d99327 q = 1) : d80477 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99327, d80477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99327, d80477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99328 q = 1) : d80478 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99328, d80478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99328, d80478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99329 q = 1) : d80479 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99329, d80479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99329, d80479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99330 q = 1) : d80480 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99330, d80480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99330, d80480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99331 q = 1) : d80481 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99331, d80481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99331, d80481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16717 (p : Pattern) (ha : d77845 p = 1) (hb : d99338 p = 1) : d80488 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2116 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8053 q = 1) (hb : d77845 q = 1) : d80214 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8053, d77845, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16544 q ha hb
    | true =>
      simp only [d8053, d77845, d80214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d8054 q = 1) (hb : d77845 q = 1) : d80215 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, d80215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8054, d80215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8055 q = 1) (hb : d77845 q = 1) : d80216 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, d80216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8055, d80216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8056 q = 1) (hb : d77845 q = 1) : d80217 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, d80217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8056, d80217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8057 q = 1) (hb : d77845 q = 1) : d80218 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, d80218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8057, d80218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d99338 q = 1) : d80488 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99338, d80488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99338, d80488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro16718 (p : Pattern) (ha : d8153 p = 1) (hb : d77844 p = 1) : d80284 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d8145 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2387 q = 1) (hb : d77842 q = 1) : d2387 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8150 q = 1) (hb : d77844 q = 1) : d80281 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8150, d77844, d80281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d8150, d77844, d80281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8151 q = 1) (hb : d77844 q = 1) : d80282 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8151, d80282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8151, d80282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8152 q = 1) (hb : d77844 q = 1) : d80283 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8152, d80283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8152, d80283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8153 q = 1) (hb : d77844 q = 1) : d80284 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8153, d80284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8153, d80284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16719 (p : Pattern) (ha : d77845 p = 1) (hb : d99349 p = 1) : d80498 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2452 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d99344 q = 1) : d80285 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d77845, d99344, d80285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16718 q hb ha
    | true =>
      simp only [d77845, d99344, d80285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99345 q = 1) : d80494 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99345, d80494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99345, d80494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99346 q = 1) : d80495 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99346, d80495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99346, d80495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99347 q = 1) : d80496 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99347, d80496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99347, d80496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99348 q = 1) : d80497 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99348, d80497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99348, d80497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d99349 q = 1) : d80498 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99349, d80498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99349, d80498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16720 (p : Pattern) (ha : d77845 p = 1) (hb : d99355 p = 1) : d80504 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8059 q = 1) (hb : d77845 q = 1) : d80220 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8059, d80220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16543 q ha hb
    | true =>
      simp only [d8059, d80220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16545 q ha hb
  have h2 (q : Pattern) (ha : d8060 q = 1) (hb : d77845 q = 1) : d80221 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8060, d80221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8060, d80221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99336 q = 1) : d80486 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99336, d80486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d99336, d80486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99337 q = 1) : d80487 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99337, d80487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99337, d80487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99339 q = 1) : d80489 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99339, d80489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99339, d80489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16717 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99340 q = 1) : d80490 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99340, d80490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99340, d80490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d99341 q = 1) : d80491 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99341, d80491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99341, d80491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d99342 q = 1) : d80492 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99342, d80492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99342, d80492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d99343 q = 1) : d80493 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99343, d80493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99343, d80493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d99350 q = 1) : d80499 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99350, d80499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99350, d80499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16719 q ha hb
  have h11 (q : Pattern) (ha : d77845 q = 1) (hb : d99351 q = 1) : d80500 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99351, d80500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99351, d80500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d99352 q = 1) : d80501 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99352, d80501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99352, d80501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d77845 q = 1) (hb : d99353 q = 1) : d80502 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99353, d80502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99353, d80502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d77845 q = 1) (hb : d99354 q = 1) : d80503 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99354, d80503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99354, d80503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d77845 q = 1) (hb : d99355 q = 1) : d80504 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99355, d80504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99355, d80504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16721 (p : Pattern) (ha : d77845 p = 1) (hb : d99361 p = 1) : d80510 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d99356 q = 1) : d80505 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99356, d80505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99356, d80505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16720 q ha hb
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d99357 q = 1) : d80506 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99357, d80506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99357, d80506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99358 q = 1) : d80507 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99358, d80507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99358, d80507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99359 q = 1) : d80508 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99359, d80508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99359, d80508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99360 q = 1) : d80509 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99360, d80509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99360, d80509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99361 q = 1) : d80510 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99361, d80510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99361, d80510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16722 (p : Pattern) (ha : d77845 p = 1) (hb : d99367 p = 1) : d80516 p = 1 := by
  have h0 (q : Pattern) (ha : d77845 q = 1) (hb : d99248 q = 1) : d80401 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d99248, d80401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16696 q ha hb
    | true =>
      simp only [d99248, d80401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16701 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d99275 q = 1) : d80427 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d99275, d80427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99275, d80427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16706 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99276 q = 1) : d80428 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d99276, d80428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99276, d80428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99303 q = 1) : d80454 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d99303, d80454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99303, d80454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16711 q ha hb
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99304 q = 1) : d80455 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d99304, d80455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99304, d80455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99305 q = 1) : d80456 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d99305, d80456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99305, d80456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d99332 q = 1) : d80482 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d99332, d80482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99332, d80482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16716 q ha hb
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d99333 q = 1) : d80483 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d99333, d80483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99333, d80483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d99334 q = 1) : d80484 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d99334, d80484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99334, d80484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d99335 q = 1) : d80485 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d99335, d80485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99335, d80485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77845 q = 1) (hb : d99362 q = 1) : d80511 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d99362, d80511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99362, d80511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16721 q ha hb
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d99363 q = 1) : d80512 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d99363, d80512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99363, d80512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77845 q = 1) (hb : d99364 q = 1) : d80513 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d99364, d80513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99364, d80513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77845 q = 1) (hb : d99365 q = 1) : d80514 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d99365, d80514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99365, d80514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77845 q = 1) (hb : d99366 q = 1) : d80515 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d99366, d80515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99366, d80515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d99367 q = 1) : d80516 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d99367, d80516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d99367, d80516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro16723 (p : Pattern) (ha : d77845 p = 1) (hb : d99373 p = 1) : d80522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d99368 q = 1) : d80517 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d99368, d80517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16722 q ha hb
    | true =>
      simp only [d99368, d80517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d99369 q = 1) : d80518 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d99369, d80518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99369, d80518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99370 q = 1) : d80519 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d99370, d80519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99370, d80519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99371 q = 1) : d80520 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d99371, d80520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99371, d80520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99372 q = 1) : d80521 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d99372, d80521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99372, d80521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99373 q = 1) : d80522 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d99373, d80522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99373, d80522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16724 (p : Pattern) (ha : d77845 p = 1) (hb : d99379 p = 1) : d80528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d99374 q = 1) : d80523 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d99374, d80523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16723 q ha hb
    | true =>
      simp only [d99374, d80523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d99375 q = 1) : d80524 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d99375, d80524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99375, d80524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99376 q = 1) : d80525 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d99376, d80525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99376, d80525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99377 q = 1) : d80526 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d99377, d80526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99377, d80526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99378 q = 1) : d80527 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d99378, d80527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99378, d80527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99379 q = 1) : d80528 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d99379, d80528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99379, d80528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16725 (p : Pattern) (ha : d77845 p = 1) (hb : d99385 p = 1) : d80534 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d99380 q = 1) : d80529 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d99380, d80529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16724 q ha hb
    | true =>
      simp only [d99380, d80529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d99381 q = 1) : d80530 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d99381, d80530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99381, d80530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99382 q = 1) : d80531 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d99382, d80531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99382, d80531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99383 q = 1) : d80532 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d99383, d80532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99383, d80532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99384 q = 1) : d80533 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d99384, d80533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99384, d80533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99385 q = 1) : d80534 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d99385, d80534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99385, d80534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16726 (p : Pattern) (ha : d77845 p = 1) (hb : d99391 p = 1) : d80540 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d99386 q = 1) : d80535 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d99386, d80535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16725 q ha hb
    | true =>
      simp only [d99386, d80535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d99387 q = 1) : d80536 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d99387, d80536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99387, d80536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99388 q = 1) : d80537 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d99388, d80537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99388, d80537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99389 q = 1) : d80538 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d99389, d80538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99389, d80538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99390 q = 1) : d80539 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d99390, d80539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99390, d80539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99391 q = 1) : d80540 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d99391, d80540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99391, d80540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16727 (p : Pattern) (ha : d77845 p = 1) (hb : d99397 p = 1) : d80546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d99392 q = 1) : d80541 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d99392, d80541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16726 q ha hb
    | true =>
      simp only [d99392, d80541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d99393 q = 1) : d80542 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d99393, d80542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99393, d80542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99394 q = 1) : d80543 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d99394, d80543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99394, d80543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99395 q = 1) : d80544 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d99395, d80544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99395, d80544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99396 q = 1) : d80545 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d99396, d80545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99396, d80545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99397 q = 1) : d80546 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d99397, d80546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99397, d80546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16728 (p : Pattern) (ha : d77845 p = 1) (hb : d99403 p = 1) : d80552 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d99398 q = 1) : d80547 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d99398, d80547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16727 q ha hb
    | true =>
      simp only [d99398, d80547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d99399 q = 1) : d80548 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d99399, d80548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99399, d80548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99400 q = 1) : d80549 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d99400, d80549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99400, d80549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99401 q = 1) : d80550 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d99401, d80550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99401, d80550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99402 q = 1) : d80551 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d99402, d80551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99402, d80551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99403 q = 1) : d80552 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d99403, d80552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99403, d80552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16729 (p : Pattern) (ha : d77845 p = 1) (hb : d99409 p = 1) : d80558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d99404 q = 1) : d80553 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d99404, d80553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16728 q ha hb
    | true =>
      simp only [d99404, d80553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d99405 q = 1) : d80554 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d99405, d80554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99405, d80554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d99406 q = 1) : d80555 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d99406, d80555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99406, d80555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d99407 q = 1) : d80556 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d99407, d80556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99407, d80556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d99408 q = 1) : d80557 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d99408, d80557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99408, d80557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d99409 q = 1) : d80558 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d99409, d80558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99409, d80558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16730 (p : Pattern) (ha : d79700 p = 1) (hb : d109668 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70872 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70877 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70880 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d70812 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d70812 q = 1) (hb : d79652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16571 q ha hb
    | true =>
      simp only [d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d70881 q = 1) (hb : d79696 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70881, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d70881, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79697 q = 1) (hb : d109665 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79697, d109665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d79697, d109665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d79698 q = 1) (hb : d109666 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79698, d109666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79698, d109666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79699 q = 1) (hb : d109667 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79699, d109667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79699, d109667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79700 q = 1) (hb : d109668 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79700, d109668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79700, d109668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16731 (p : Pattern) (ha : d79707 p = 1) (hb : d109672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70872 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70877 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70880 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70812 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70812 q = 1) (hb : d79652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16571 q ha hb
    | true =>
      simp only [d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70881 q = 1) (hb : d79696 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70881, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d70881, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d79697 q = 1) (hb : d109665 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79697, d109665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d79697, d109665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79698 q = 1) (hb : d109666 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79698, d109666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79698, d109666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79699 q = 1) (hb : d109667 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79699, d109667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79699, d109667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70889 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d70892 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d70893 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d70818 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d70818 q = 1) (hb : d79659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16573 q ha hb
    | true =>
      simp only [d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d70894 q = 1) (hb : d79703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70894, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d70894, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d79704 q = 1) (hb : d109669 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79704, d109669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d79704, d109669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h17 (q : Pattern) (ha : d79705 q = 1) (hb : d109670 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79705, d109670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79705, d109670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d79706 q = 1) (hb : d109671 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79706, d109671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d79706, d109671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d79707 q = 1) (hb : d109672 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79707, d109672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79707, d109672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro16732 (p : Pattern) (ha : d80353 p = 1) (hb : d109681 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70893 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70818 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d70818 q = 1) (hb : d79659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16573 q ha hb
    | true =>
      simp only [d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d70894 q = 1) (hb : d79703 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70894, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d70894, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d79704 q = 1) (hb : d109669 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79704, d109669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d79704, d109669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d79705 q = 1) (hb : d109679 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79705, d109679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79705, d109679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79706 q = 1) (hb : d109680 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79706, d109680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79706, d109680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80353 q = 1) (hb : d109681 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80353, d109681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80353, d109681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16733 (p : Pattern) (ha : d80363 p = 1) (hb : d109690 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70913 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70836 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d70836 q = 1) (hb : d79679 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16576 q ha hb
    | true =>
      simp only [d79679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d70914 q = 1) (hb : d80359 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d70914, d80359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d70914, d80359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d80360 q = 1) (hb : d109687 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80360, d109687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d80360, d109687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80361 q = 1) (hb : d109688 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80361, d109688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80361, d109688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80362 q = 1) (hb : d109689 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80362, d109689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80362, d109689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80363 q = 1) (hb : d109690 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80363, d109690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80363, d109690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16734 (p : Pattern) (ha : d80369 p = 1) (hb : d109696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70867 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79708 q = 1) (hb : d109673 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79708, d109673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16730 q ha hb
    | true =>
      simp only [d79708, d109673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16731 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109675 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d79709 q = 1) (hb : d109676 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79709, d109676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79709, d109676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80351 q = 1) (hb : d109677 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80351, d109677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80351, d109677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80352 q = 1) (hb : d109678 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80352, d109678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80352, d109678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80354 q = 1) (hb : d109682 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80354, d109682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80354, d109682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16732 q ha hb
  have h8 (q : Pattern) (ha : d80355 q = 1) (hb : d109683 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80355, d109683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d80355, d109683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d80356 q = 1) (hb : d109684 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80356, d109684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80356, d109684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d80357 q = 1) (hb : d109685 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80357, d109685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80357, d109685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d80358 q = 1) (hb : d109686 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80358, d109686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80358, d109686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d80364 q = 1) (hb : d109691 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80364, d109691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80364, d109691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16733 q ha hb
  have h13 (q : Pattern) (ha : d80365 q = 1) (hb : d109692 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80365, d109692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80365, d109692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d80366 q = 1) (hb : d109693 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80366, d109693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80366, d109693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d80367 q = 1) (hb : d109694 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80367, d109694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d80367, d109694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d80368 q = 1) (hb : d109695 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80368, d109695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80368, d109695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d80369 q = 1) (hb : d109696 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d80369, d109696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80369, d109696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16735 (p : Pattern) (ha : d80375 p = 1) (hb : d109702 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70852 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d80370 q = 1) (hb : d109697 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d80370, d109697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80370, d109697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16734 q ha hb
  have h3 (q : Pattern) (ha : d80371 q = 1) (hb : d109698 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d80371, d109698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80371, d109698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80372 q = 1) (hb : d109699 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d80372, d109699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80372, d109699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d80373 q = 1) (hb : d109700 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d80373, d109700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80373, d109700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80374 q = 1) (hb : d109701 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d80374, d109701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80374, d109701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80375 q = 1) (hb : d109702 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d80375, d109702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80375, d109702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16736 (p : Pattern) (ha : d79792 p = 1) (hb : d109710 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70954 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70959 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d109705 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d70933 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d70933 q = 1) (hb : d79787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16595 q ha hb
    | true =>
      simp only [d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79788 q = 1) (hb : d109706 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79788, d109706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79788, d109706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d79789 q = 1) (hb : d109707 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79789, d109707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79789, d109707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d79790 q = 1) (hb : d109708 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79790, d109708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79790, d109708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79791 q = 1) (hb : d109709 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79791, d109709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79791, d109709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79792 q = 1) (hb : d109710 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79792, d109710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79792, d109710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16737 (p : Pattern) (ha : d79801 p = 1) (hb : d109716 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70954 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d70959 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109705 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d70933 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d70933 q = 1) (hb : d79787 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16595 q ha hb
    | true =>
      simp only [d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79788 q = 1) (hb : d109706 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79788, d109706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79788, d109706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d79789 q = 1) (hb : d109707 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79789, d109707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79789, d109707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79790 q = 1) (hb : d109708 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79790, d109708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79790, d109708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79791 q = 1) (hb : d109709 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79791, d109709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79791, d109709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d70972 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d70975 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d109711 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d70941 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d70941 q = 1) (hb : d79796 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16597 q ha hb
    | true =>
      simp only [d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d79797 q = 1) (hb : d109712 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79797, d109712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d79797, d109712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d79798 q = 1) (hb : d109713 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79798, d109713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d79798, d109713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h17 (q : Pattern) (ha : d79799 q = 1) (hb : d109714 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79799, d109714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79799, d109714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d79800 q = 1) (hb : d109715 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79800, d109715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d79800, d109715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d79801 q = 1) (hb : d109716 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79801, d109716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79801, d109716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro16738 (p : Pattern) (ha : d80378 p = 1) (hb : d109725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109711 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d70941 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d70941 q = 1) (hb : d79796 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16597 q ha hb
    | true =>
      simp only [d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d79797 q = 1) (hb : d109712 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79797, d109712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79797, d109712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79798 q = 1) (hb : d109713 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79798, d109713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79798, d109713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d79799 q = 1) (hb : d109723 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79799, d109723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79799, d109723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79800 q = 1) (hb : d109724 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79800, d109724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79800, d109724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80378 q = 1) (hb : d109725 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80378, d109725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80378, d109725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16739 (p : Pattern) (ha : d71000 p = 1) (hb : d79866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d684 q = 1) (hb : d52388 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro71 q ha hb
    | true =>
      simp only [d684, d52388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d685 q = 1) (hb : d52389 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d685, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d685, d52389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52389 q = 1) (hb : d79863 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d70998 q = 1) (hb : d79864 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d70998, d79864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d70998, d79864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d70999 q = 1) (hb : d79865 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d70999, d79865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d70999, d79865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d71000 q = 1) (hb : d79866 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71000, d79866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71000, d79866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro16740 (p : Pattern) (ha : d80388 p = 1) (hb : d109738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109733 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71000 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71000 q = 1) (hb : d79867 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16739 q ha hb
    | true =>
      simp only [d79867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d80384 q = 1) (hb : d109734 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80384, d109734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80384, d109734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d80385 q = 1) (hb : d109735 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80385, d109735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80385, d109735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80386 q = 1) (hb : d109736 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80386, d109736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80386, d109736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80387 q = 1) (hb : d109737 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80387, d109737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80387, d109737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80388 q = 1) (hb : d109738 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80388, d109738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80388, d109738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16741 (p : Pattern) (ha : d80394 p = 1) (hb : d109744 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d70949 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79802 q = 1) (hb : d109717 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79802, d109717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16736 q ha hb
    | true =>
      simp only [d79802, d109717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16737 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109719 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d79803 q = 1) (hb : d109720 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79803, d109720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79803, d109720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80376 q = 1) (hb : d109721 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80376, d109721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80376, d109721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80377 q = 1) (hb : d109722 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80377, d109722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80377, d109722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80379 q = 1) (hb : d109726 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80379, d109726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80379, d109726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16738 q ha hb
  have h8 (q : Pattern) (ha : d80380 q = 1) (hb : d109727 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80380, d109727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d80380, d109727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d80381 q = 1) (hb : d109728 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80381, d109728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80381, d109728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d80382 q = 1) (hb : d109729 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80382, d109729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80382, d109729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d80383 q = 1) (hb : d109730 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80383, d109730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80383, d109730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d80389 q = 1) (hb : d109739 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80389, d109739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80389, d109739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16740 q ha hb
  have h13 (q : Pattern) (ha : d80390 q = 1) (hb : d109740 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80390, d109740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80390, d109740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d80391 q = 1) (hb : d109741 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80391, d109741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80391, d109741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d80392 q = 1) (hb : d109742 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80392, d109742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d80392, d109742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d80393 q = 1) (hb : d109743 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80393, d109743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80393, d109743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d80394 q = 1) (hb : d109744 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d80394, d109744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80394, d109744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16742 (p : Pattern) (ha : d80400 p = 1) (hb : d109750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80395 q = 1) (hb : d109745 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d80395, d109745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80395, d109745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16741 q ha hb
  have h2 (q : Pattern) (ha : d80396 q = 1) (hb : d109746 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d80396, d109746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80396, d109746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80397 q = 1) (hb : d109747 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d80397, d109747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80397, d109747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80398 q = 1) (hb : d109748 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d80398, d109748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80398, d109748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d80399 q = 1) (hb : d109749 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d80399, d109749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80399, d109749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80400 q = 1) (hb : d109750 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d80400, d109750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80400, d109750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16743 (p : Pattern) (ha : d79895 p = 1) (hb : d109759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71043 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71048 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d109754 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d71022 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d71022 q = 1) (hb : d79890 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16613 q ha hb
    | true =>
      simp only [d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d79891 q = 1) (hb : d109755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79891, d109755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d79891, d109755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d79892 q = 1) (hb : d109756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79892, d109756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d79892, d109756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d79893 q = 1) (hb : d109757 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79893, d109757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79893, d109757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79894 q = 1) (hb : d109758 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79894, d109758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79894, d109758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d79895 q = 1) (hb : d109759 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79895, d109759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79895, d109759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16744 (p : Pattern) (ha : d79904 p = 1) (hb : d109765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d71043 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d71048 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d71022 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d71022 q = 1) (hb : d79890 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16613 q ha hb
    | true =>
      simp only [d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79891 q = 1) (hb : d109755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79891, d109755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d79891, d109755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d79892 q = 1) (hb : d109756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79892, d109756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d79892, d109756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d79893 q = 1) (hb : d109757 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79893, d109757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79893, d109757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d79894 q = 1) (hb : d109758 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79894, d109758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79894, d109758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d71061 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d71064 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d109760 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d71030 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d71030 q = 1) (hb : d79899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16615 q ha hb
    | true =>
      simp only [d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d79900 q = 1) (hb : d109761 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79900, d109761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d79900, d109761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d79901 q = 1) (hb : d109762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79901, d109762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d79901, d109762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h17 (q : Pattern) (ha : d79902 q = 1) (hb : d109763 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79902, d109763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d79902, d109763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d79903 q = 1) (hb : d109764 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79903, d109764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d79903, d109764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d79904 q = 1) (hb : d109765 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d79904, d109765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d79904, d109765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro16745 (p : Pattern) (ha : d80404 p = 1) (hb : d109774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109760 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71030 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71030 q = 1) (hb : d79899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16615 q ha hb
    | true =>
      simp only [d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d79900 q = 1) (hb : d109761 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d79900, d109761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79900, d109761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d79901 q = 1) (hb : d109762 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d79901, d109762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d79901, d109762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d79902 q = 1) (hb : d109772 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d79902, d109772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79902, d109772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d79903 q = 1) (hb : d109773 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d79903, d109773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79903, d109773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80404 q = 1) (hb : d109774 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80404, d109774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80404, d109774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16746 (p : Pattern) (ha : d71089 p = 1) (hb : d79969 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1006 q = 1) (hb : d52625 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro117 q ha hb
    | true =>
      simp only [d1006, d52625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1007 q = 1) (hb : d52626 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1007, d52626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d52626 q = 1) (hb : d79966 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d79966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d79966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d71087 q = 1) (hb : d79967 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d71087, d79967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d71087, d79967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h6 (q : Pattern) (ha : d71088 q = 1) (hb : d79968 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d71088, d79968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d71088, d79968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d71089 q = 1) (hb : d79969 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d71089, d79969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d71089, d79969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h7 p ha hb
theorem andIntro16747 (p : Pattern) (ha : d80414 p = 1) (hb : d109787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d109782 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d71089 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d71089 q = 1) (hb : d79970 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d79970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16746 q ha hb
    | true =>
      simp only [d79970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d80410 q = 1) (hb : d109783 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d80410, d109783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d80410, d109783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d80411 q = 1) (hb : d109784 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d80411, d109784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80411, d109784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d80412 q = 1) (hb : d109785 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d80412, d109785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80412, d109785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80413 q = 1) (hb : d109786 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d80413, d109786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80413, d109786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d80414 q = 1) (hb : d109787 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d80414, d109787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80414, d109787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16748 (p : Pattern) (ha : d80420 p = 1) (hb : d109793 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d71038 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79905 q = 1) (hb : d109766 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d79905, d109766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16743 q ha hb
    | true =>
      simp only [d79905, d109766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16744 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109768 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d79906 q = 1) (hb : d109769 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d79906, d109769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d79906, d109769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d80402 q = 1) (hb : d109770 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80402, d109770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d80402, d109770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80403 q = 1) (hb : d109771 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80403, d109771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80403, d109771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d80405 q = 1) (hb : d109775 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80405, d109775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80405, d109775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16745 q ha hb
  have h8 (q : Pattern) (ha : d80406 q = 1) (hb : d109776 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80406, d109776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d80406, d109776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h9 (q : Pattern) (ha : d80407 q = 1) (hb : d109777 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80407, d109777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d80407, d109777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h10 (q : Pattern) (ha : d80408 q = 1) (hb : d109778 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80408, d109778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d80408, d109778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d80409 q = 1) (hb : d109779 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80409, d109779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d80409, d109779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d80415 q = 1) (hb : d109788 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d80415, d109788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d80415, d109788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16747 q ha hb
  have h13 (q : Pattern) (ha : d80416 q = 1) (hb : d109789 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d80416, d109789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d80416, d109789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h14 (q : Pattern) (ha : d80417 q = 1) (hb : d109790 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d80417, d109790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d80417, d109790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h15 (q : Pattern) (ha : d80418 q = 1) (hb : d109791 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d80418, d109791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d80418, d109791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h16 (q : Pattern) (ha : d80419 q = 1) (hb : d109792 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d80419, d109792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d80419, d109792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d80420 q = 1) (hb : d109793 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d80420, d109793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d80420, d109793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16749 (p : Pattern) (ha : d80426 p = 1) (hb : d109799 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d80421 q = 1) (hb : d109794 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d80421, d109794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80421, d109794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16748 q ha hb
  have h2 (q : Pattern) (ha : d80422 q = 1) (hb : d109795 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d80422, d109795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80422, d109795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d80423 q = 1) (hb : d109796 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d80423, d109796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80423, d109796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d80424 q = 1) (hb : d109797 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d80424, d109797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80424, d109797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d80425 q = 1) (hb : d109798 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d80425, d109798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80425, d109798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d80426 q = 1) (hb : d109799 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d80426, d109799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d80426, d109799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
