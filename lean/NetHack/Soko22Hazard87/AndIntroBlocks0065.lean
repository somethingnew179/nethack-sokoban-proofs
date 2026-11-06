import NetHack.Soko22Hazard87.AndIntroBlocks0064
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro16250 (p : Pattern) (ha : d11666 p = 1) (hb : d108984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11687 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11696 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11709 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11661 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11662 q = 1) (hb : d108980 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d108980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11662, d108980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d11749 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11663 q = 1) (hb : d108981 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d108981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11663, d108981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11664 q = 1) (hb : d108982 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d108982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11664, d108982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11665 q = 1) (hb : d108983 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d108983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11665, d108983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11666 q = 1) (hb : d108984 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11666, d108984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11666, d108984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16251 (p : Pattern) (ha : d11676 p = 1) (hb : d108989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11687 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11696 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11709 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11661 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11662 q = 1) (hb : d108980 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11662, d108980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11662, d108980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d11749 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11663 q = 1) (hb : d108981 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11663, d108981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11663, d108981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11664 q = 1) (hb : d108982 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11664, d108982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11664, d108982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11665 q = 1) (hb : d108983 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11665, d108983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11665, d108983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d11759 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d11764 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d11766 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d11671 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d11672 q = 1) (hb : d108985 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11672, d108985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11672, d108985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11773 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d11673 q = 1) (hb : d108986 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11673, d108986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11673, d108986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11674 q = 1) (hb : d108987 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11674, d108987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11674, d108987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11675 q = 1) (hb : d108988 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11675, d108988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11675, d108988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d11676 q = 1) (hb : d108989 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11676, d108989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11676, d108989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro16252 (p : Pattern) (ha : d108996 p = 1) (hb : d109221 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11766 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11671 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11672 q = 1) (hb : d108985 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11672, d108985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11672, d108985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11773 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11673 q = 1) (hb : d108986 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11673, d108986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11673, d108986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11674 q = 1) (hb : d108994 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11674, d108994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11674, d108994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11675 q = 1) (hb : d108995 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11675, d108995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11675, d108995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d108996 q = 1) (hb : d109221 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d108996, d109221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108996, d109221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro16253 (p : Pattern) (ha : d109006 p = 1) (hb : d109232 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11837 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109227 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d109002 q = 1) (hb : d109228 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109002, d109228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109002, d109228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11877 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109003 q = 1) (hb : d109229 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109003, d109229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109003, d109229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d109004 q = 1) (hb : d109230 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109004, d109230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109004, d109230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109005 q = 1) (hb : d109231 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109005, d109231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109005, d109231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109006 q = 1) (hb : d109232 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109006, d109232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109006, d109232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16254 (p : Pattern) (ha : d109012 p = 1) (hb : d109238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11679 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11677 q = 1) (hb : d108990 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11677, d108990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16250 q ha hb
    | true =>
      simp only [d11677, d108990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16251 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11791 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11678 q = 1) (hb : d108991 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11678, d108991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11678, d108991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d108992 q = 1) (hb : d109219 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108992, d109219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d108992, d109219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108993 q = 1) (hb : d109220 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d108993, d109220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d108993, d109220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d108997 q = 1) (hb : d109222 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d108997, d109222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d108997, d109222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16252 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d11800 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d108998 q = 1) (hb : d109223 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d108998, d109223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d108998, d109223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d108999 q = 1) (hb : d109224 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d108999, d109224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d108999, d109224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d109000 q = 1) (hb : d109225 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109000, d109225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109000, d109225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d109001 q = 1) (hb : d109226 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109001, d109226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109001, d109226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109007 q = 1) (hb : d109233 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109007, d109233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109007, d109233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16253 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d11893 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d109008 q = 1) (hb : d109234 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109008, d109234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109008, d109234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d109009 q = 1) (hb : d109235 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109009, d109235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109009, d109235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d109010 q = 1) (hb : d109236 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109010, d109236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109010, d109236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d109011 q = 1) (hb : d109237 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109011, d109237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109011, d109237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d109012 q = 1) (hb : d109238 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109012, d109238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109012, d109238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro16255 (p : Pattern) (ha : d109018 p = 1) (hb : d109244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109013 q = 1) (hb : d109239 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109013, d109239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109013, d109239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16254 q ha hb
  have h2 (q : Pattern) (ha : d109014 q = 1) (hb : d109240 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109014, d109240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109014, d109240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109015 q = 1) (hb : d109241 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109015, d109241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109015, d109241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109016 q = 1) (hb : d109242 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109016, d109242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109016, d109242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109017 q = 1) (hb : d109243 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109017, d109243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109017, d109243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109018 q = 1) (hb : d109244 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109018, d109244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109018, d109244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16256 (p : Pattern) (ha : d11938 p = 1) (hb : d109027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11959 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11968 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11981 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d11933 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11934 q = 1) (hb : d109023 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d109023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11934, d109023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d12021 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d11935 q = 1) (hb : d109024 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d109024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11935, d109024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11936 q = 1) (hb : d109025 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d109025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11936, d109025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d11937 q = 1) (hb : d109026 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d109026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11937, d109026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11938 q = 1) (hb : d109027 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11938, d109027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11938, d109027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16257 (p : Pattern) (ha : d11948 p = 1) (hb : d109032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11959 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d11968 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11981 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d11933 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d11934 q = 1) (hb : d109023 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11934, d109023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11934, d109023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d12021 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d11935 q = 1) (hb : d109024 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11935, d109024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11935, d109024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11936 q = 1) (hb : d109025 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11936, d109025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11936, d109025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11937 q = 1) (hb : d109026 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11937, d109026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11937, d109026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d12031 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d12036 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d12038 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d11943 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d11944 q = 1) (hb : d109028 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11944, d109028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11944, d109028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12045 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d11945 q = 1) (hb : d109029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11945, d109029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d11945, d109029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d11946 q = 1) (hb : d109030 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11946, d109030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11946, d109030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d11947 q = 1) (hb : d109031 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11947, d109031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11947, d109031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d11948 q = 1) (hb : d109032 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11948, d109032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d11948, d109032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro16258 (p : Pattern) (ha : d109039 p = 1) (hb : d109251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12038 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d11943 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11944 q = 1) (hb : d109028 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11944, d109028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11944, d109028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12045 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d11945 q = 1) (hb : d109029 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11945, d109029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11945, d109029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11946 q = 1) (hb : d109037 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11946, d109037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11946, d109037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11947 q = 1) (hb : d109038 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11947, d109038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11947, d109038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109039 q = 1) (hb : d109251 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109039, d109251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109039, d109251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro16259 (p : Pattern) (ha : d109049 p = 1) (hb : d109262 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d12109 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d109257 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d109045 q = 1) (hb : d109258 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109045, d109258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d109045, d109258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d12149 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109046 q = 1) (hb : d109259 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109046, d109259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109046, d109259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d109047 q = 1) (hb : d109260 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109047, d109260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109047, d109260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109048 q = 1) (hb : d109261 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109048, d109261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109048, d109261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d109049 q = 1) (hb : d109262 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109049, d109262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109049, d109262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16260 (p : Pattern) (ha : d109055 p = 1) (hb : d109268 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d11951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11949 q = 1) (hb : d109033 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11949, d109033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16256 q ha hb
    | true =>
      simp only [d11949, d109033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16257 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d12063 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d11950 q = 1) (hb : d109034 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11950, d109034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11950, d109034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d109035 q = 1) (hb : d109249 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109035, d109249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d109035, d109249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109036 q = 1) (hb : d109250 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109036, d109250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d109036, d109250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109040 q = 1) (hb : d109252 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109040, d109252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109040, d109252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16258 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d12072 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d109041 q = 1) (hb : d109253 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109041, d109253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109041, d109253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d109042 q = 1) (hb : d109254 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109042, d109254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109042, d109254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h11 (q : Pattern) (ha : d109043 q = 1) (hb : d109255 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109043, d109255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109043, d109255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h12 (q : Pattern) (ha : d109044 q = 1) (hb : d109256 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109044, d109256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109044, d109256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109050 q = 1) (hb : d109263 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109050, d109263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109050, d109263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16259 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d12165 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d109051 q = 1) (hb : d109264 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109051, d109264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109051, d109264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d109052 q = 1) (hb : d109265 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109052, d109265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109052, d109265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h17 (q : Pattern) (ha : d109053 q = 1) (hb : d109266 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109053, d109266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d109053, d109266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h18 (q : Pattern) (ha : d109054 q = 1) (hb : d109267 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109054, d109267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d109054, d109267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h19 (q : Pattern) (ha : d109055 q = 1) (hb : d109268 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109055, d109268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109055, d109268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro16261 (p : Pattern) (ha : d109061 p = 1) (hb : d109274 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109056 q = 1) (hb : d109269 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109056, d109269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109056, d109269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16260 q ha hb
  have h2 (q : Pattern) (ha : d109057 q = 1) (hb : d109270 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109057, d109270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109057, d109270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109058 q = 1) (hb : d109271 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109058, d109271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109058, d109271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109059 q = 1) (hb : d109272 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109059, d109272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109059, d109272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109060 q = 1) (hb : d109273 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109060, d109273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109060, d109273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109061 q = 1) (hb : d109274 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109061, d109274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109061, d109274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16262 (p : Pattern) (ha : d109067 p = 1) (hb : d109280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d108896 q = 1) (hb : d109161 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108896, d109161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16231 q ha hb
    | true =>
      simp only [d108896, d109161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16237 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d108936 q = 1) (hb : d109188 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108936, d109188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108936, d109188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16243 q ha hb
  have h3 (q : Pattern) (ha : d108937 q = 1) (hb : d109189 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108937, d109189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d108937, d109189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d108977 q = 1) (hb : d109216 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d108977, d109216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108977, d109216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16249 q ha hb
  have h5 (q : Pattern) (ha : d108978 q = 1) (hb : d109217 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d108978, d109217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d108978, d109217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d108979 q = 1) (hb : d109218 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d108979, d109218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d108979, d109218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109019 q = 1) (hb : d109245 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109019, d109245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109019, d109245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16255 q ha hb
  have h8 (q : Pattern) (ha : d109020 q = 1) (hb : d109246 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109020, d109246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109020, d109246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d109021 q = 1) (hb : d109247 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109021, d109247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109021, d109247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109022 q = 1) (hb : d109248 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109022, d109248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109022, d109248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d109062 q = 1) (hb : d109275 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d109062, d109275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109062, d109275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16261 q ha hb
  have h12 (q : Pattern) (ha : d109063 q = 1) (hb : d109276 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d109063, d109276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109063, d109276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d109064 q = 1) (hb : d109277 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d109064, d109277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109064, d109277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d109065 q = 1) (hb : d109278 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d109065, d109278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109065, d109278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d109066 q = 1) (hb : d109279 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d109066, d109279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109066, d109279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d109067 q = 1) (hb : d109280 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d109067, d109280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d109067, d109280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro16263 (p : Pattern) (ha : d109073 p = 1) (hb : d109286 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109068 q = 1) (hb : d109281 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d109068, d109281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16262 q ha hb
    | true =>
      simp only [d109068, d109281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109069 q = 1) (hb : d109282 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d109069, d109282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109069, d109282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109070 q = 1) (hb : d109283 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d109070, d109283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109070, d109283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109071 q = 1) (hb : d109284 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d109071, d109284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109071, d109284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109072 q = 1) (hb : d109285 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d109072, d109285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109072, d109285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109073 q = 1) (hb : d109286 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d109073, d109286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109073, d109286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16264 (p : Pattern) (ha : d109079 p = 1) (hb : d109292 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109074 q = 1) (hb : d109287 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d109074, d109287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16263 q ha hb
    | true =>
      simp only [d109074, d109287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109075 q = 1) (hb : d109288 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d109075, d109288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109075, d109288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109076 q = 1) (hb : d109289 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d109076, d109289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109076, d109289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109077 q = 1) (hb : d109290 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d109077, d109290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109077, d109290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109078 q = 1) (hb : d109291 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d109078, d109291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109078, d109291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109079 q = 1) (hb : d109292 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d109079, d109292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109079, d109292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16265 (p : Pattern) (ha : d109085 p = 1) (hb : d109298 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109080 q = 1) (hb : d109293 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d109080, d109293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16264 q ha hb
    | true =>
      simp only [d109080, d109293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109081 q = 1) (hb : d109294 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d109081, d109294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109081, d109294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109082 q = 1) (hb : d109295 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d109082, d109295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109082, d109295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109083 q = 1) (hb : d109296 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d109083, d109296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109083, d109296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109084 q = 1) (hb : d109297 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d109084, d109297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109084, d109297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109085 q = 1) (hb : d109298 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d109085, d109298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109085, d109298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16266 (p : Pattern) (ha : d109091 p = 1) (hb : d109304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109086 q = 1) (hb : d109299 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d109086, d109299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16265 q ha hb
    | true =>
      simp only [d109086, d109299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109087 q = 1) (hb : d109300 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d109087, d109300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109087, d109300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109088 q = 1) (hb : d109301 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d109088, d109301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109088, d109301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109089 q = 1) (hb : d109302 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d109089, d109302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109089, d109302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109090 q = 1) (hb : d109303 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d109090, d109303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109090, d109303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109091 q = 1) (hb : d109304 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d109091, d109304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109091, d109304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16267 (p : Pattern) (ha : d109097 p = 1) (hb : d109310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109092 q = 1) (hb : d109305 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d109092, d109305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16266 q ha hb
    | true =>
      simp only [d109092, d109305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109093 q = 1) (hb : d109306 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d109093, d109306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109093, d109306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109094 q = 1) (hb : d109307 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d109094, d109307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109094, d109307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109095 q = 1) (hb : d109308 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d109095, d109308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109095, d109308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109096 q = 1) (hb : d109309 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d109096, d109309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109096, d109309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109097 q = 1) (hb : d109310 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d109097, d109310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109097, d109310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16268 (p : Pattern) (ha : d109103 p = 1) (hb : d109316 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109098 q = 1) (hb : d109311 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d109098, d109311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16267 q ha hb
    | true =>
      simp only [d109098, d109311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109099 q = 1) (hb : d109312 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d109099, d109312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109099, d109312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109100 q = 1) (hb : d109313 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d109100, d109313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109100, d109313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109101 q = 1) (hb : d109314 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d109101, d109314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109101, d109314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109102 q = 1) (hb : d109315 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d109102, d109315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109102, d109315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109103 q = 1) (hb : d109316 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d109103, d109316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109103, d109316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16269 (p : Pattern) (ha : d109109 p = 1) (hb : d109322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109104 q = 1) (hb : d109317 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d109104, d109317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16268 q ha hb
    | true =>
      simp only [d109104, d109317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d109105 q = 1) (hb : d109318 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d109105, d109318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109105, d109318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109106 q = 1) (hb : d109319 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d109106, d109319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109106, d109319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109107 q = 1) (hb : d109320 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d109107, d109320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109107, d109320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109108 q = 1) (hb : d109321 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d109108, d109321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109108, d109321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d109109 q = 1) (hb : d109322 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d109109, d109322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109109, d109322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16270 (p : Pattern) (ha : d74849 p = 1) (hb : d109328 p = 1) : d74849 p = 1 := by
  have h0 (q : Pattern) (ha : d74849 q = 1) (hb : d109328 q = 1) : d74849 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro16271 (p : Pattern) (ha : d53865 p = 1) (hb : d109328 p = 1) : d53865 p = 1 := by
  have h0 (q : Pattern) (ha : d53865 q = 1) (hb : d109328 q = 1) : d53865 q = 1 := by
    exact ha
  exact h0 p ha hb
theorem andIntro16272 (p : Pattern) (ha : d7247 p = 1) (hb : d83662 p = 1) : d7347 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7243 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7244 q = 1) (hb : d83662 q = 1) : d7344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7244, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7245 q = 1) (hb : d83662 q = 1) : d7345 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7245, d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7246 q = 1) (hb : d83662 q = 1) : d7346 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7246, d7346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7246, d7346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7247 q = 1) (hb : d83662 q = 1) : d7347 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7247, d7347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7247, d7347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16273 (p : Pattern) (ha : d83662 p = 1) (hb : d85394 p = 1) : d84548 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d120 q = 1) (hb : d83662 q = 1) : d120 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d126 q = 1) (hb : d83662 q = 1) : d126 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d42 q = 1) (hb : d83662 q = 1) : d42 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7248 q = 1) (hb : d83662 q = 1) : d84543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16272 q ha hb
    | true =>
      simp only [d7248, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85390 q = 1) : d84544 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85390, d84544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d85390, d84544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d83662 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d85391 q = 1) : d84545 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85391, d84545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85391, d84545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d83662 q = 1) (hb : d85392 q = 1) : d84546 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85392, d84546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85392, d84546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83662 q = 1) (hb : d85393 q = 1) : d84547 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85393, d84547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85393, d84547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83662 q = 1) (hb : d85394 q = 1) : d84548 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85394, d84548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85394, d84548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16274 (p : Pattern) (ha : d7254 p = 1) (hb : d83662 p = 1) : d7368 p = 1 := by
  have h0 (q : Pattern) (ha : d7243 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7244 q = 1) (hb : d83662 q = 1) : d7344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7244, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7245 q = 1) (hb : d83662 q = 1) : d7345 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7245, d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7246 q = 1) (hb : d83662 q = 1) : d7346 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7246, d7346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7246, d7346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7254 q = 1) (hb : d83662 q = 1) : d7368 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7254, d7368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7254, d7368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16275 (p : Pattern) (ha : d83662 p = 1) (hb : d85399 p = 1) : d84554 p = 1 := by
  have h0 (q : Pattern) (ha : d120 q = 1) (hb : d83662 q = 1) : d120 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d126 q = 1) (hb : d83662 q = 1) : d126 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d42 q = 1) (hb : d83662 q = 1) : d42 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7248 q = 1) (hb : d83662 q = 1) : d84543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16272 q ha hb
    | true =>
      simp only [d7248, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85390 q = 1) : d84544 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85390, d84544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d85390, d84544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d44 q = 1) (hb : d83662 q = 1) : d44 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d85391 q = 1) : d84545 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85391, d84545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85391, d84545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d83662 q = 1) (hb : d85392 q = 1) : d84546 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85392, d84546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85392, d84546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83662 q = 1) (hb : d85393 q = 1) : d84547 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85393, d84547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85393, d84547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d198 q = 1) (hb : d83662 q = 1) : d198 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d202 q = 1) (hb : d83662 q = 1) : d202 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d49 q = 1) (hb : d83662 q = 1) : d49 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d7255 q = 1) (hb : d83662 q = 1) : d84549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16274 q ha hb
    | true =>
      simp only [d7255, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85395 q = 1) : d84550 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85395, d84550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
    | true =>
      simp only [d85395, d84550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d51 q = 1) (hb : d83662 q = 1) : d51 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d83662 q = 1) (hb : d85396 q = 1) : d84551 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85396, d84551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85396, d84551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d83662 q = 1) (hb : d85397 q = 1) : d84552 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85397, d84552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85397, d84552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d83662 q = 1) (hb : d85398 q = 1) : d84553 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85398, d84553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85398, d84553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d83662 q = 1) (hb : d85399 q = 1) : d84554 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85399, d84554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85399, d84554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro16276 (p : Pattern) (ha : d83662 p = 1) (hb : d85406 p = 1) : d84561 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d83662 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7255 q = 1) (hb : d83662 q = 1) : d84549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16274 q ha hb
    | true =>
      simp only [d7255, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d85395 q = 1) : d84550 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85395, d84550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85395, d84550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d51 q = 1) (hb : d83662 q = 1) : d51 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85396 q = 1) : d84551 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85396, d84551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85396, d84551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85404 q = 1) : d84559 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85404, d84559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85404, d84559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d85405 q = 1) : d84560 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85405, d84560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85405, d84560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83662 q = 1) (hb : d85406 q = 1) : d84561 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85406, d84561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85406, d84561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16277 (p : Pattern) (ha : d7280 p = 1) (hb : d83662 p = 1) : d7411 p = 1 := by
  have h0 (q : Pattern) (ha : d7276 q = 1) (hb : d77842 q = 1) : d7276 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d79 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7277 q = 1) (hb : d83662 q = 1) : d7408 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7277, d83662, d7408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7277, d83662, d7408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7278 q = 1) (hb : d83662 q = 1) : d7409 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7278, d7409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7278, d7409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7279 q = 1) (hb : d83662 q = 1) : d7410 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7279, d7410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7279, d7410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7280 q = 1) (hb : d83662 q = 1) : d7411 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7280, d7411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7280, d7411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16278 (p : Pattern) (ha : d83662 p = 1) (hb : d85416 p = 1) : d84572 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d83662 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7281 q = 1) (hb : d83662 q = 1) : d84567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7281, d84567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16277 q ha hb
    | true =>
      simp only [d7281, d84567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d85412 q = 1) : d84568 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85412, d84568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85412, d84568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d85 q = 1) (hb : d83662 q = 1) : d85 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85413 q = 1) : d84569 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85413, d84569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85413, d84569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85414 q = 1) : d84570 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85414, d84570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85414, d84570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d85415 q = 1) : d84571 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85415, d84571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85415, d84571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d83662 q = 1) (hb : d85416 q = 1) : d84572 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85416, d84572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85416, d84572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16279 (p : Pattern) (ha : d83662 p = 1) (hb : d85422 p = 1) : d84578 p = 1 := by
  have h0 (q : Pattern) (ha : d114 q = 1) (hb : d83662 q = 1) : d114 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d85400 q = 1) : d84555 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85400, d84555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16273 q ha hb
    | true =>
      simp only [d85400, d84555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16275 q ha hb
  have h2 (q : Pattern) (ha : d214 q = 1) (hb : d83662 q = 1) : d214 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d85401 q = 1) : d84556 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85401, d84556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85401, d84556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85402 q = 1) : d84557 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85402, d84557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85402, d84557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85403 q = 1) : d84558 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85403, d84558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85403, d84558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d85407 q = 1) : d84562 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85407, d84562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d85407, d84562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16276 q ha hb
  have h8 (q : Pattern) (ha : d83662 q = 1) (hb : d85408 q = 1) : d84563 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85408, d84563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d85408, d84563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d83662 q = 1) (hb : d85409 q = 1) : d84564 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85409, d84564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85409, d84564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d83662 q = 1) (hb : d85410 q = 1) : d84565 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85410, d84565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85410, d84565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85411 q = 1) : d84566 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85411, d84566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85411, d84566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d83662 q = 1) (hb : d85417 q = 1) : d84573 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85417, d84573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d85417, d84573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16278 q ha hb
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d85418 q = 1) : d84574 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85418, d84574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85418, d84574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85419 q = 1) : d84575 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85419, d84575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85419, d84575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d85420 q = 1) : d84576 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85420, d84576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85420, d84576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d83662 q = 1) (hb : d85421 q = 1) : d84577 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85421, d84577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85421, d84577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d83662 q = 1) (hb : d85422 q = 1) : d84578 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85422, d84578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85422, d84578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16280 (p : Pattern) (ha : d7302 p = 1) (hb : d83662 p = 1) : d84588 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d83662 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7248 q = 1) (hb : d83662 q = 1) : d84543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16272 q ha hb
    | true =>
      simp only [d7248, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7298 q = 1) (hb : d83662 q = 1) : d84584 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7299 q = 1) (hb : d83662 q = 1) : d84585 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7299, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7300 q = 1) (hb : d83662 q = 1) : d84586 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7301 q = 1) (hb : d83662 q = 1) : d84587 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7302 q = 1) (hb : d83662 q = 1) : d84588 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7302, d84588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7302, d84588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16281 (p : Pattern) (ha : d7309 p = 1) (hb : d83662 p = 1) : d84595 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d83662 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7248 q = 1) (hb : d83662 q = 1) : d84543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16272 q ha hb
    | true =>
      simp only [d7248, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7298 q = 1) (hb : d83662 q = 1) : d84584 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7299 q = 1) (hb : d83662 q = 1) : d84585 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7299, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7300 q = 1) (hb : d83662 q = 1) : d84586 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7301 q = 1) (hb : d83662 q = 1) : d84587 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d49 q = 1) (hb : d83662 q = 1) : d49 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7255 q = 1) (hb : d83662 q = 1) : d84549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16274 q ha hb
    | true =>
      simp only [d7255, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7305 q = 1) (hb : d83662 q = 1) : d84591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7305, d84591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7305, d84591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7306 q = 1) (hb : d83662 q = 1) : d84592 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7306, d84592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7306, d84592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7307 q = 1) (hb : d83662 q = 1) : d84593 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7307, d84593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7307, d84593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d7308 q = 1) (hb : d83662 q = 1) : d84594 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7308, d84594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7308, d84594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7309 q = 1) (hb : d83662 q = 1) : d84595 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7309, d84595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7309, d84595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16282 (p : Pattern) (ha : d7376 p = 1) (hb : d83662 p = 1) : d84633 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d42 q = 1) (hb : d83662 q = 1) : d42 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7248 q = 1) (hb : d83662 q = 1) : d84543 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16272 q ha hb
    | true =>
      simp only [d7248, d84543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7298 q = 1) (hb : d83662 q = 1) : d84584 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d84584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7299 q = 1) (hb : d83662 q = 1) : d84585 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7299, d84585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7300 q = 1) (hb : d83662 q = 1) : d84586 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d84586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7301 q = 1) (hb : d83662 q = 1) : d84587 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d84587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d103 q = 1) (hb : d83662 q = 1) : d103 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7376 q = 1) (hb : d83662 q = 1) : d84633 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7376, d84633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7376, d84633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16283 (p : Pattern) (ha : d7314 p = 1) (hb : d83662 p = 1) : d84600 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7243 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7244 q = 1) (hb : d83662 q = 1) : d7344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7244, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7245 q = 1) (hb : d83662 q = 1) : d7345 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7245, d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7313 q = 1) (hb : d83662 q = 1) : d84599 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7313, d84599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7313, d84599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7314 q = 1) (hb : d83662 q = 1) : d84600 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7314, d84600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7314, d84600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16284 (p : Pattern) (ha : d7321 p = 1) (hb : d83662 p = 1) : d84607 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7243 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7244 q = 1) (hb : d83662 q = 1) : d7344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7244, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7319 q = 1) (hb : d83662 q = 1) : d84605 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7319, d84605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7319, d84605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7320 q = 1) (hb : d83662 q = 1) : d84606 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7320, d84606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7320, d84606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7321 q = 1) (hb : d83662 q = 1) : d84607 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7321, d84607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7321, d84607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16285 (p : Pattern) (ha : d7332 p = 1) (hb : d83662 p = 1) : d7486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7328 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7243 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7329 q = 1) (hb : d83662 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7329, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7329, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7330 q = 1) (hb : d83662 q = 1) : d7484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7330, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7330, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7331 q = 1) (hb : d83662 q = 1) : d7485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7331, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7331, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7332 q = 1) (hb : d83662 q = 1) : d7486 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7332, d7486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7332, d7486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16286 (p : Pattern) (ha : d83662 p = 1) (hb : d85432 p = 1) : d84616 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d83662 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7315 q = 1) (hb : d83662 q = 1) : d84601 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7315, d84601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16283 q ha hb
    | true =>
      simp only [d7315, d84601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7316 q = 1) (hb : d83662 q = 1) : d84602 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7316, d84602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7316, d84602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7317 q = 1) (hb : d83662 q = 1) : d84603 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7317, d84603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7317, d84603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7318 q = 1) (hb : d83662 q = 1) : d84604 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7318, d84604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7318, d84604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d83662 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7322 q = 1) (hb : d83662 q = 1) : d84608 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7322, d84608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16284 q ha hb
    | true =>
      simp only [d7322, d84608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7323 q = 1) (hb : d83662 q = 1) : d84609 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7323, d84609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7323, d84609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7324 q = 1) (hb : d83662 q = 1) : d84610 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7324, d84610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7324, d84610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7333 q = 1) (hb : d83662 q = 1) : d84611 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7333, d84611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16285 q ha hb
    | true =>
      simp only [d7333, d84611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16272 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85428 q = 1) : d84612 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85428, d84612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85428, d84612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d7349 q = 1) (hb : d83662 q = 1) : d7349 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d85429 q = 1) : d84613 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85429, d84613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85429, d84613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85430 q = 1) : d84614 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85430, d84614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85430, d84614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d85431 q = 1) : d84615 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85431, d84615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85431, d84615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83662 q = 1) (hb : d85432 q = 1) : d84616 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85432, d84616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85432, d84616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro16287 (p : Pattern) (ha : d7354 p = 1) (hb : d83662 p = 1) : d84617 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7243 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7244 q = 1) (hb : d83662 q = 1) : d7344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7244, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7245 q = 1) (hb : d83662 q = 1) : d7345 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7245, d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7313 q = 1) (hb : d83662 q = 1) : d84599 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7313, d84599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7313, d84599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7354 q = 1) (hb : d83662 q = 1) : d84617 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7354, d84617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7354, d84617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16288 (p : Pattern) (ha : d7359 p = 1) (hb : d83662 p = 1) : d84622 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7243 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d38 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7244 q = 1) (hb : d83662 q = 1) : d7344 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7244, d83662, d7344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7319 q = 1) (hb : d83662 q = 1) : d84605 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7319, d84605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7319, d84605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7320 q = 1) (hb : d83662 q = 1) : d84606 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7320, d84606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7320, d84606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7359 q = 1) (hb : d83662 q = 1) : d84622 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7359, d84622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7359, d84622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16289 (p : Pattern) (ha : d7363 p = 1) (hb : d83662 p = 1) : d7507 p = 1 := by
  have h0 (q : Pattern) (ha : d7328 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7243 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7329 q = 1) (hb : d83662 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7329, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7329, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7330 q = 1) (hb : d83662 q = 1) : d7484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7330, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7330, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7331 q = 1) (hb : d83662 q = 1) : d7485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7331, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7331, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7363 q = 1) (hb : d83662 q = 1) : d7507 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7363, d7507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7363, d7507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16290 (p : Pattern) (ha : d83662 p = 1) (hb : d85437 p = 1) : d84631 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d116 q = 1) (hb : d83662 q = 1) : d116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7315 q = 1) (hb : d83662 q = 1) : d84601 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7315, d84601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16283 q ha hb
    | true =>
      simp only [d7315, d84601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7316 q = 1) (hb : d83662 q = 1) : d84602 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7316, d84602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7316, d84602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7317 q = 1) (hb : d83662 q = 1) : d84603 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7317, d84603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7317, d84603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7318 q = 1) (hb : d83662 q = 1) : d84604 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7318, d84604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7318, d84604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d123 q = 1) (hb : d83662 q = 1) : d123 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7322 q = 1) (hb : d83662 q = 1) : d84608 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7322, d84608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16284 q ha hb
    | true =>
      simp only [d7322, d84608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7323 q = 1) (hb : d83662 q = 1) : d84609 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7323, d84609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7323, d84609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7324 q = 1) (hb : d83662 q = 1) : d84610 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7324, d84610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7324, d84610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7333 q = 1) (hb : d83662 q = 1) : d84611 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7333, d84611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16285 q ha hb
    | true =>
      simp only [d7333, d84611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16272 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85428 q = 1) : d84612 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85428, d84612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85428, d84612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d7349 q = 1) (hb : d83662 q = 1) : d7349 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d85429 q = 1) : d84613 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85429, d84613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85429, d84613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85430 q = 1) : d84614 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85430, d84614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85430, d84614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d85431 q = 1) : d84615 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85431, d84615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85431, d84615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d194 q = 1) (hb : d83662 q = 1) : d194 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d7355 q = 1) (hb : d83662 q = 1) : d84618 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7355, d84618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16287 q ha hb
    | true =>
      simp only [d7355, d84618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7356 q = 1) (hb : d83662 q = 1) : d84619 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7356, d84619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7356, d84619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d7357 q = 1) (hb : d83662 q = 1) : d84620 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7357, d84620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d7357, d84620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d7358 q = 1) (hb : d83662 q = 1) : d84621 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7358, d84621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7358, d84621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d199 q = 1) (hb : d83662 q = 1) : d199 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d7360 q = 1) (hb : d83662 q = 1) : d84623 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7360, d84623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16288 q ha hb
    | true =>
      simp only [d7360, d84623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d7361 q = 1) (hb : d83662 q = 1) : d84624 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7361, d84624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7361, d84624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d7362 q = 1) (hb : d83662 q = 1) : d84625 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7362, d84625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d7362, d84625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d7364 q = 1) (hb : d83662 q = 1) : d84626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7364, d84626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16289 q ha hb
    | true =>
      simp only [d7364, d84626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16274 q ha hb
  have h26 (q : Pattern) (ha : d83662 q = 1) (hb : d85433 q = 1) : d84627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85433, d84627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d85433, d84627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d7370 q = 1) (hb : d83662 q = 1) : d7370 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d83662 q = 1) (hb : d85434 q = 1) : d84628 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85434, d84628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d85434, d84628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d83662 q = 1) (hb : d85435 q = 1) : d84629 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85435, d84629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d85435, d84629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d83662 q = 1) (hb : d85436 q = 1) : d84630 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85436, d84630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d85436, d84630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d83662 q = 1) (hb : d85437 q = 1) : d84631 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85437, d84631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85437, d84631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro16291 (p : Pattern) (ha : d83662 p = 1) (hb : d85444 p = 1) : d84640 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7364 q = 1) (hb : d83662 q = 1) : d84626 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7364, d84626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16289 q ha hb
    | true =>
      simp only [d7364, d84626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16274 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85433 q = 1) : d84627 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85433, d84627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85433, d84627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d7370 q = 1) (hb : d83662 q = 1) : d7370 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85434 q = 1) : d84628 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85434, d84628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85434, d84628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85442 q = 1) : d84638 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85442, d84638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85442, d84638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85443 q = 1) : d84639 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85443, d84639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85443, d84639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d85444 q = 1) : d84640 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85444, d84640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85444, d84640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16292 (p : Pattern) (ha : d7396 p = 1) (hb : d83662 p = 1) : d7554 p = 1 := by
  have h0 (q : Pattern) (ha : d7392 q = 1) (hb : d77842 q = 1) : d7392 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7276 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7393 q = 1) (hb : d83662 q = 1) : d7551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7393, d83662, d7551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7393, d83662, d7551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7394 q = 1) (hb : d83662 q = 1) : d7552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7394, d7552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7394, d7552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7395 q = 1) (hb : d83662 q = 1) : d7553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7395, d7553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7395, d7553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7396 q = 1) (hb : d83662 q = 1) : d7554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7396, d7554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7396, d7554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16293 (p : Pattern) (ha : d83662 p = 1) (hb : d85454 p = 1) : d84651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7397 q = 1) (hb : d83662 q = 1) : d84646 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7397, d84646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16292 q ha hb
    | true =>
      simp only [d7397, d84646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16277 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85450 q = 1) : d84647 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85450, d84647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85450, d84647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d7413 q = 1) (hb : d83662 q = 1) : d7413 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85451 q = 1) : d84648 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85451, d84648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85451, d84648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85452 q = 1) : d84649 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85452, d84649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85452, d84649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85453 q = 1) : d84650 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85453, d84650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85453, d84650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d85454 q = 1) : d84651 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85454, d84651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85454, d84651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16294 (p : Pattern) (ha : d83662 p = 1) (hb : d85460 p = 1) : d84657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7303 q = 1) (hb : d83662 q = 1) : d84589 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7303, d84589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7303, d84589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16280 q ha hb
  have h2 (q : Pattern) (ha : d7304 q = 1) (hb : d83662 q = 1) : d84590 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7304, d84590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7304, d84590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7310 q = 1) (hb : d83662 q = 1) : d84596 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7310, d84596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16280 q ha hb
    | true =>
      simp only [d7310, d84596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16281 q ha hb
  have h4 (q : Pattern) (ha : d7311 q = 1) (hb : d83662 q = 1) : d84597 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7311, d84597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7311, d84597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7312 q = 1) (hb : d83662 q = 1) : d84598 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7312, d84598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7312, d84598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85438 q = 1) : d84632 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85438, d84632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16286 q ha hb
    | true =>
      simp only [d85438, d84632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16290 q ha hb
  have h7 (q : Pattern) (ha : d111 q = 1) (hb : d83662 q = 1) : d111 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7377 q = 1) (hb : d83662 q = 1) : d84634 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7377, d84634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16282 q ha hb
    | true =>
      simp only [d7377, d84634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83662 q = 1) (hb : d85439 q = 1) : d84635 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85439, d84635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85439, d84635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d83662 q = 1) (hb : d85440 q = 1) : d84636 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85440, d84636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85440, d84636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85441 q = 1) : d84637 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85441, d84637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85441, d84637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d83662 q = 1) (hb : d85445 q = 1) : d84641 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85445, d84641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85445, d84641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16291 q ha hb
  have h13 (q : Pattern) (ha : d407 q = 1) (hb : d83662 q = 1) : d407 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85446 q = 1) : d84642 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85446, d84642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85446, d84642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d85447 q = 1) : d84643 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85447, d84643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85447, d84643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d83662 q = 1) (hb : d85448 q = 1) : d84644 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85448, d84644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85448, d84644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d83662 q = 1) (hb : d85449 q = 1) : d84645 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85449, d84645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85449, d84645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d83662 q = 1) (hb : d85455 q = 1) : d84652 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85455, d84652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85455, d84652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16293 q ha hb
  have h19 (q : Pattern) (ha : d463 q = 1) (hb : d83662 q = 1) : d463 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d83662 q = 1) (hb : d85456 q = 1) : d84653 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85456, d84653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85456, d84653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d83662 q = 1) (hb : d85457 q = 1) : d84654 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85457, d84654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85457, d84654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d83662 q = 1) (hb : d85458 q = 1) : d84655 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85458, d84655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85458, d84655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83662 q = 1) (hb : d85459 q = 1) : d84656 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85459, d84656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85459, d84656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d83662 q = 1) (hb : d85460 q = 1) : d84657 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85460, d84657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85460, d84657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro16295 (p : Pattern) (ha : d83662 p = 1) (hb : d85466 p = 1) : d84663 p = 1 := by
  have h0 (q : Pattern) (ha : d99 q = 1) (hb : d83662 q = 1) : d99 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85423 q = 1) : d84579 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85423, d84579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85423, d84579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16279 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d85424 q = 1) : d84580 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85424, d84580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85424, d84580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85425 q = 1) : d84581 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85425, d84581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85425, d84581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85426 q = 1) : d84582 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85426, d84582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85426, d84582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85427 q = 1) : d84583 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85427, d84583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85427, d84583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d85461 q = 1) : d84658 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85461, d84658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85461, d84658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16294 q ha hb
  have h8 (q : Pattern) (ha : d83662 q = 1) (hb : d85462 q = 1) : d84659 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85462, d84659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85462, d84659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83662 q = 1) (hb : d85463 q = 1) : d84660 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85463, d84660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85463, d84660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83662 q = 1) (hb : d85464 q = 1) : d84661 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85464, d84661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85464, d84661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85465 q = 1) : d84662 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85465, d84662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85465, d84662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d83662 q = 1) (hb : d85466 q = 1) : d84663 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85466, d84663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85466, d84663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro16296 (p : Pattern) (ha : d7433 p = 1) (hb : d83662 p = 1) : d7486 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7328 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d483 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7430 q = 1) (hb : d83662 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7430, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7431 q = 1) (hb : d83662 q = 1) : d7484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7431, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7432 q = 1) (hb : d83662 q = 1) : d7485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7432, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7432, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7433 q = 1) (hb : d83662 q = 1) : d7486 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7433, d7486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7433, d7486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16297 (p : Pattern) (ha : d7439 p = 1) (hb : d83662 p = 1) : d84669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d83662 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7434 q = 1) (hb : d83662 q = 1) : d84664 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16296 q ha hb
    | true =>
      simp only [d7434, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7435 q = 1) (hb : d83662 q = 1) : d84665 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7436 q = 1) (hb : d83662 q = 1) : d84666 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7436, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7437 q = 1) (hb : d83662 q = 1) : d84667 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7438 q = 1) (hb : d83662 q = 1) : d84668 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7439 q = 1) (hb : d83662 q = 1) : d84669 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7439, d84669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7439, d84669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16298 (p : Pattern) (ha : d7442 p = 1) (hb : d83662 p = 1) : d7507 p = 1 := by
  have h0 (q : Pattern) (ha : d7328 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d483 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7430 q = 1) (hb : d83662 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7430, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7431 q = 1) (hb : d83662 q = 1) : d7484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7431, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7432 q = 1) (hb : d83662 q = 1) : d7485 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7432, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7432, d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7442 q = 1) (hb : d83662 q = 1) : d7507 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7442, d7507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7442, d7507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16299 (p : Pattern) (ha : d7448 p = 1) (hb : d83662 p = 1) : d84677 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d83662 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7434 q = 1) (hb : d83662 q = 1) : d84664 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16296 q ha hb
    | true =>
      simp only [d7434, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7435 q = 1) (hb : d83662 q = 1) : d84665 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7436 q = 1) (hb : d83662 q = 1) : d84666 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7436, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7437 q = 1) (hb : d83662 q = 1) : d84667 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7438 q = 1) (hb : d83662 q = 1) : d84668 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d501 q = 1) (hb : d83662 q = 1) : d501 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7443 q = 1) (hb : d83662 q = 1) : d84672 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7443, d84672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16298 q ha hb
    | true =>
      simp only [d7443, d84672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7444 q = 1) (hb : d83662 q = 1) : d84673 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7444, d84673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7444, d84673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7445 q = 1) (hb : d83662 q = 1) : d84674 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7445, d84674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7445, d84674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7446 q = 1) (hb : d83662 q = 1) : d84675 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7446, d84675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7446, d84675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d7447 q = 1) (hb : d83662 q = 1) : d84676 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7447, d84676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7447, d84676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7448 q = 1) (hb : d83662 q = 1) : d84677 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7448, d84677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7448, d84677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16300 (p : Pattern) (ha : d7515 p = 1) (hb : d83662 p = 1) : d84720 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d491 q = 1) (hb : d83662 q = 1) : d491 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7434 q = 1) (hb : d83662 q = 1) : d84664 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16296 q ha hb
    | true =>
      simp only [d7434, d84664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7435 q = 1) (hb : d83662 q = 1) : d84665 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d84665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7436 q = 1) (hb : d83662 q = 1) : d84666 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7436, d84666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7437 q = 1) (hb : d83662 q = 1) : d84667 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d84667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7438 q = 1) (hb : d83662 q = 1) : d84668 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d84668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d637 q = 1) (hb : d83662 q = 1) : d637 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7515 q = 1) (hb : d83662 q = 1) : d84720 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7515, d84720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7515, d84720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16301 (p : Pattern) (ha : d7453 p = 1) (hb : d83662 p = 1) : d84682 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7328 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d483 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7430 q = 1) (hb : d83662 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7430, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7431 q = 1) (hb : d83662 q = 1) : d7484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7431, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7452 q = 1) (hb : d83662 q = 1) : d84681 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7452, d84681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7452, d84681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7453 q = 1) (hb : d83662 q = 1) : d84682 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7453, d84682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7453, d84682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16302 (p : Pattern) (ha : d7460 p = 1) (hb : d83662 p = 1) : d84689 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7328 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d483 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7430 q = 1) (hb : d83662 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7430, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7458 q = 1) (hb : d83662 q = 1) : d84687 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7458, d84687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7458, d84687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7459 q = 1) (hb : d83662 q = 1) : d84688 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7459, d84688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7459, d84688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7460 q = 1) (hb : d83662 q = 1) : d84689 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7460, d84689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7460, d84689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16303 (p : Pattern) (ha : d7471 p = 1) (hb : d83662 p = 1) : d84696 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7467 q = 1) (hb : d77842 q = 1) : d7467 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7328 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7468 q = 1) (hb : d83662 q = 1) : d84693 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7468, d83662, d84693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7468, d83662, d84693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7469 q = 1) (hb : d83662 q = 1) : d84694 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7469, d84694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7469, d84694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7470 q = 1) (hb : d83662 q = 1) : d84695 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7470, d84695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7470, d84695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7471 q = 1) (hb : d83662 q = 1) : d84696 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7471, d84696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7471, d84696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16304 (p : Pattern) (ha : d83662 p = 1) (hb : d85471 p = 1) : d84702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d514 q = 1) (hb : d83662 q = 1) : d514 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7454 q = 1) (hb : d83662 q = 1) : d84683 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7454, d84683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16301 q ha hb
    | true =>
      simp only [d7454, d84683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7455 q = 1) (hb : d83662 q = 1) : d84684 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7455, d84684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7455, d84684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7456 q = 1) (hb : d83662 q = 1) : d84685 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7456, d84685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7456, d84685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7457 q = 1) (hb : d83662 q = 1) : d84686 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7457, d84686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7457, d84686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d83662 q = 1) : d524 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7461 q = 1) (hb : d83662 q = 1) : d84690 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7461, d84690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16302 q ha hb
    | true =>
      simp only [d7461, d84690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7462 q = 1) (hb : d83662 q = 1) : d84691 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7462, d84691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7462, d84691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7463 q = 1) (hb : d83662 q = 1) : d84692 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7463, d84692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7463, d84692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7472 q = 1) (hb : d83662 q = 1) : d84697 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7472, d84697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16303 q ha hb
    | true =>
      simp only [d7472, d84697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16296 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85467 q = 1) : d84698 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85467, d84698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85467, d84698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d7488 q = 1) (hb : d83662 q = 1) : d7488 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d85468 q = 1) : d84699 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85468, d84699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85468, d84699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85469 q = 1) : d84700 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85469, d84700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85469, d84700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d85470 q = 1) : d84701 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85470, d84701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85470, d84701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83662 q = 1) (hb : d85471 q = 1) : d84702 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85471, d84702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85471, d84702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro16305 (p : Pattern) (ha : d7493 p = 1) (hb : d83662 p = 1) : d84703 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7328 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d483 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7430 q = 1) (hb : d83662 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7430, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7431 q = 1) (hb : d83662 q = 1) : d7484 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7431, d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7452 q = 1) (hb : d83662 q = 1) : d84681 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7452, d84681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7452, d84681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7493 q = 1) (hb : d83662 q = 1) : d84703 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7493, d84703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7493, d84703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16306 (p : Pattern) (ha : d7498 p = 1) (hb : d83662 p = 1) : d84708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7328 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d483 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7430 q = 1) (hb : d83662 q = 1) : d7483 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7430, d83662, d7483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7458 q = 1) (hb : d83662 q = 1) : d84687 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7458, d84687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7458, d84687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7459 q = 1) (hb : d83662 q = 1) : d84688 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7459, d84688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7459, d84688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7498 q = 1) (hb : d83662 q = 1) : d84708 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7498, d84708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7498, d84708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16307 (p : Pattern) (ha : d7502 p = 1) (hb : d83662 p = 1) : d84712 p = 1 := by
  have h0 (q : Pattern) (ha : d7467 q = 1) (hb : d77842 q = 1) : d7467 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7468 q = 1) (hb : d83662 q = 1) : d84693 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7468, d83662, d84693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7468, d83662, d84693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7469 q = 1) (hb : d83662 q = 1) : d84694 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7469, d84694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7469, d84694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7470 q = 1) (hb : d83662 q = 1) : d84695 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7470, d84695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7470, d84695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7502 q = 1) (hb : d83662 q = 1) : d84712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7502, d84712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7502, d84712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16308 (p : Pattern) (ha : d83662 p = 1) (hb : d85476 p = 1) : d84718 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d514 q = 1) (hb : d83662 q = 1) : d514 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7454 q = 1) (hb : d83662 q = 1) : d84683 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7454, d84683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16301 q ha hb
    | true =>
      simp only [d7454, d84683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7455 q = 1) (hb : d83662 q = 1) : d84684 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7455, d84684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7455, d84684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7456 q = 1) (hb : d83662 q = 1) : d84685 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7456, d84685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7456, d84685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7457 q = 1) (hb : d83662 q = 1) : d84686 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7457, d84686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7457, d84686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d524 q = 1) (hb : d83662 q = 1) : d524 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7461 q = 1) (hb : d83662 q = 1) : d84690 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7461, d84690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16302 q ha hb
    | true =>
      simp only [d7461, d84690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7462 q = 1) (hb : d83662 q = 1) : d84691 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7462, d84691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7462, d84691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7463 q = 1) (hb : d83662 q = 1) : d84692 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7463, d84692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7463, d84692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7472 q = 1) (hb : d83662 q = 1) : d84697 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7472, d84697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16303 q ha hb
    | true =>
      simp only [d7472, d84697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16296 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85467 q = 1) : d84698 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85467, d84698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85467, d84698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d7488 q = 1) (hb : d83662 q = 1) : d7488 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d85468 q = 1) : d84699 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85468, d84699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85468, d84699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85469 q = 1) : d84700 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85469, d84700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85469, d84700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d85470 q = 1) : d84701 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85470, d84701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85470, d84701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d610 q = 1) (hb : d83662 q = 1) : d610 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d7494 q = 1) (hb : d83662 q = 1) : d84704 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7494, d84704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16305 q ha hb
    | true =>
      simp only [d7494, d84704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7495 q = 1) (hb : d83662 q = 1) : d84705 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7495, d84705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7495, d84705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d7496 q = 1) (hb : d83662 q = 1) : d84706 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7496, d84706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d7496, d84706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d7497 q = 1) (hb : d83662 q = 1) : d84707 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7497, d84707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7497, d84707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d616 q = 1) (hb : d83662 q = 1) : d616 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d7499 q = 1) (hb : d83662 q = 1) : d84709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7499, d84709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16306 q ha hb
    | true =>
      simp only [d7499, d84709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d7500 q = 1) (hb : d83662 q = 1) : d84710 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7500, d84710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7500, d84710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d7501 q = 1) (hb : d83662 q = 1) : d84711 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7501, d84711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d7501, d84711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d7503 q = 1) (hb : d83662 q = 1) : d84713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7503, d84713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16307 q ha hb
    | true =>
      simp only [d7503, d84713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16298 q ha hb
  have h26 (q : Pattern) (ha : d83662 q = 1) (hb : d85472 q = 1) : d84714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85472, d84714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d85472, d84714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d7509 q = 1) (hb : d83662 q = 1) : d7509 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d83662 q = 1) (hb : d85473 q = 1) : d84715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85473, d84715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d85473, d84715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d83662 q = 1) (hb : d85474 q = 1) : d84716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85474, d84716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d85474, d84716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d83662 q = 1) (hb : d85475 q = 1) : d84717 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85475, d84717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d85475, d84717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d83662 q = 1) (hb : d85476 q = 1) : d84718 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85476, d84718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85476, d84718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro16309 (p : Pattern) (ha : d83662 p = 1) (hb : d85483 p = 1) : d84727 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7503 q = 1) (hb : d83662 q = 1) : d84713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7503, d84713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16307 q ha hb
    | true =>
      simp only [d7503, d84713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16298 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85472 q = 1) : d84714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85472, d84714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85472, d84714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d7509 q = 1) (hb : d83662 q = 1) : d7509 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85473 q = 1) : d84715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85473, d84715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85473, d84715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85481 q = 1) : d84725 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85481, d84725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85481, d84725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85482 q = 1) : d84726 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85482, d84726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85482, d84726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d85483 q = 1) : d84727 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85483, d84727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85483, d84727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16310 (p : Pattern) (ha : d7535 p = 1) (hb : d83662 p = 1) : d84736 p = 1 := by
  have h0 (q : Pattern) (ha : d7531 q = 1) (hb : d77842 q = 1) : d7531 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7392 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7532 q = 1) (hb : d83662 q = 1) : d84733 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7532, d83662, d84733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7532, d83662, d84733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7533 q = 1) (hb : d83662 q = 1) : d84734 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7533, d84734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7533, d84734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7534 q = 1) (hb : d83662 q = 1) : d84735 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7534, d84735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7534, d84735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7535 q = 1) (hb : d83662 q = 1) : d84736 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7535, d84736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7535, d84736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16311 (p : Pattern) (ha : d7539 p = 1) (hb : d83662 p = 1) : d7554 p = 1 := by
  have h0 (q : Pattern) (ha : d7392 q = 1) (hb : d77842 q = 1) : d7392 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d685 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7536 q = 1) (hb : d83662 q = 1) : d7551 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7536, d83662, d7551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7536, d83662, d7551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7537 q = 1) (hb : d83662 q = 1) : d7552 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7537, d7552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7537, d7552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7538 q = 1) (hb : d83662 q = 1) : d7553 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7538, d7553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7538, d7553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7539 q = 1) (hb : d83662 q = 1) : d7554 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7539, d7554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7539, d7554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16312 (p : Pattern) (ha : d83662 p = 1) (hb : d85493 p = 1) : d84742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7540 q = 1) (hb : d83662 q = 1) : d84737 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7540, d84737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16310 q ha hb
    | true =>
      simp only [d7540, d84737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16311 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85489 q = 1) : d84738 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85489, d84738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85489, d84738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d7556 q = 1) (hb : d83662 q = 1) : d7556 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85490 q = 1) : d84739 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85490, d84739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85490, d84739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85491 q = 1) : d84740 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85491, d84740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85491, d84740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85492 q = 1) : d84741 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85492, d84741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85492, d84741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d85493 q = 1) : d84742 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85493, d84742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85493, d84742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16313 (p : Pattern) (ha : d83662 p = 1) (hb : d85499 p = 1) : d84748 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7440 q = 1) (hb : d83662 q = 1) : d84670 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7440, d84670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7440, d84670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16297 q ha hb
  have h2 (q : Pattern) (ha : d7441 q = 1) (hb : d83662 q = 1) : d84671 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7441, d84671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7441, d84671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7449 q = 1) (hb : d83662 q = 1) : d84678 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7449, d84678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16297 q ha hb
    | true =>
      simp only [d7449, d84678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16299 q ha hb
  have h4 (q : Pattern) (ha : d7450 q = 1) (hb : d83662 q = 1) : d84679 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7450, d84679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7450, d84679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7451 q = 1) (hb : d83662 q = 1) : d84680 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7451, d84680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7451, d84680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85477 q = 1) : d84719 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85477, d84719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16304 q ha hb
    | true =>
      simp only [d85477, d84719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16308 q ha hb
  have h7 (q : Pattern) (ha : d644 q = 1) (hb : d83662 q = 1) : d644 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7516 q = 1) (hb : d83662 q = 1) : d84721 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7516, d84721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16300 q ha hb
    | true =>
      simp only [d7516, d84721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83662 q = 1) (hb : d85478 q = 1) : d84722 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85478, d84722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85478, d84722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d83662 q = 1) (hb : d85479 q = 1) : d84723 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85479, d84723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85479, d84723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85480 q = 1) : d84724 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85480, d84724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85480, d84724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d83662 q = 1) (hb : d85484 q = 1) : d84728 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85484, d84728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85484, d84728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16309 q ha hb
  have h13 (q : Pattern) (ha : d654 q = 1) (hb : d83662 q = 1) : d654 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85485 q = 1) : d84729 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85485, d84729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85485, d84729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d85486 q = 1) : d84730 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85486, d84730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85486, d84730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d83662 q = 1) (hb : d85487 q = 1) : d84731 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85487, d84731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85487, d84731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d83662 q = 1) (hb : d85488 q = 1) : d84732 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85488, d84732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85488, d84732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d83662 q = 1) (hb : d85494 q = 1) : d84743 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85494, d84743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85494, d84743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16312 q ha hb
  have h19 (q : Pattern) (ha : d737 q = 1) (hb : d83662 q = 1) : d737 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d83662 q = 1) (hb : d85495 q = 1) : d84744 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85495, d84744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85495, d84744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d83662 q = 1) (hb : d85496 q = 1) : d84745 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85496, d84745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85496, d84745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d83662 q = 1) (hb : d85497 q = 1) : d84746 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85497, d84746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85497, d84746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83662 q = 1) (hb : d85498 q = 1) : d84747 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85498, d84747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85498, d84747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d83662 q = 1) (hb : d85499 q = 1) : d84748 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85499, d84748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85499, d84748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro16314 (p : Pattern) (ha : d83662 p = 1) (hb : d85505 p = 1) : d84754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d85500 q = 1) : d84749 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85500, d84749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85500, d84749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16313 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85501 q = 1) : d84750 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85501, d84750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85501, d84750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d85502 q = 1) : d84751 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85502, d84751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85502, d84751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85503 q = 1) : d84752 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85503, d84752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85503, d84752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85504 q = 1) : d84753 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85504, d84753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85504, d84753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85505 q = 1) : d84754 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85505, d84754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85505, d84754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16315 (p : Pattern) (ha : d7581 p = 1) (hb : d83662 p = 1) : d7634 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7577 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d775 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7578 q = 1) (hb : d83662 q = 1) : d7631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7578, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7579 q = 1) (hb : d83662 q = 1) : d7632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7579, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7580 q = 1) (hb : d83662 q = 1) : d7633 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7580, d7633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7580, d7633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7581 q = 1) (hb : d83662 q = 1) : d7634 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7581, d7634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7581, d7634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16316 (p : Pattern) (ha : d7587 p = 1) (hb : d83662 p = 1) : d84761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d83662 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7582 q = 1) (hb : d83662 q = 1) : d84756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d84756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16315 q ha hb
    | true =>
      simp only [d7582, d84756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7583 q = 1) (hb : d83662 q = 1) : d84757 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d84757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d84757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7584 q = 1) (hb : d83662 q = 1) : d84758 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d84758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7584, d84758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7585 q = 1) (hb : d83662 q = 1) : d84759 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d84759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d84759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7586 q = 1) (hb : d83662 q = 1) : d84760 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d84760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d84760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7587 q = 1) (hb : d83662 q = 1) : d84761 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7587, d84761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7587, d84761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16317 (p : Pattern) (ha : d7590 p = 1) (hb : d83662 p = 1) : d7655 p = 1 := by
  have h0 (q : Pattern) (ha : d7577 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d775 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7578 q = 1) (hb : d83662 q = 1) : d7631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7578, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7579 q = 1) (hb : d83662 q = 1) : d7632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7579, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7580 q = 1) (hb : d83662 q = 1) : d7633 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7580, d7633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7580, d7633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7590 q = 1) (hb : d83662 q = 1) : d7655 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7590, d7655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7590, d7655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16318 (p : Pattern) (ha : d7596 p = 1) (hb : d83662 p = 1) : d84769 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d83662 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7582 q = 1) (hb : d83662 q = 1) : d84756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d84756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16315 q ha hb
    | true =>
      simp only [d7582, d84756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7583 q = 1) (hb : d83662 q = 1) : d84757 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d84757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d84757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7584 q = 1) (hb : d83662 q = 1) : d84758 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d84758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7584, d84758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7585 q = 1) (hb : d83662 q = 1) : d84759 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d84759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d84759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7586 q = 1) (hb : d83662 q = 1) : d84760 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d84760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d84760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d793 q = 1) (hb : d83662 q = 1) : d793 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7591 q = 1) (hb : d83662 q = 1) : d84764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7591, d84764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16317 q ha hb
    | true =>
      simp only [d7591, d84764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7592 q = 1) (hb : d83662 q = 1) : d84765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, d84765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7592, d84765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7593 q = 1) (hb : d83662 q = 1) : d84766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, d84766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7593, d84766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7594 q = 1) (hb : d83662 q = 1) : d84767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, d84767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7594, d84767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d7595 q = 1) (hb : d83662 q = 1) : d84768 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, d84768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7595, d84768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7596 q = 1) (hb : d83662 q = 1) : d84769 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7596, d84769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7596, d84769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16319 (p : Pattern) (ha : d7663 p = 1) (hb : d83662 p = 1) : d84812 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d783 q = 1) (hb : d83662 q = 1) : d783 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7582 q = 1) (hb : d83662 q = 1) : d84756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d84756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16315 q ha hb
    | true =>
      simp only [d7582, d84756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7583 q = 1) (hb : d83662 q = 1) : d84757 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d84757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d84757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7584 q = 1) (hb : d83662 q = 1) : d84758 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d84758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7584, d84758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7585 q = 1) (hb : d83662 q = 1) : d84759 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d84759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d84759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7586 q = 1) (hb : d83662 q = 1) : d84760 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d84760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d84760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d943 q = 1) (hb : d83662 q = 1) : d943 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7663 q = 1) (hb : d83662 q = 1) : d84812 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7663, d84812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7663, d84812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16320 (p : Pattern) (ha : d7601 p = 1) (hb : d83662 p = 1) : d84774 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7577 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d775 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7578 q = 1) (hb : d83662 q = 1) : d7631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7578, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7579 q = 1) (hb : d83662 q = 1) : d7632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7579, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7600 q = 1) (hb : d83662 q = 1) : d84773 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7600, d84773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7600, d84773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7601 q = 1) (hb : d83662 q = 1) : d84774 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7601, d84774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7601, d84774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16321 (p : Pattern) (ha : d7608 p = 1) (hb : d83662 p = 1) : d84781 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7577 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d775 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7578 q = 1) (hb : d83662 q = 1) : d7631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7578, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7606 q = 1) (hb : d83662 q = 1) : d84779 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7606, d84779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7606, d84779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7607 q = 1) (hb : d83662 q = 1) : d84780 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7607, d84780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7607, d84780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7608 q = 1) (hb : d83662 q = 1) : d84781 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7608, d84781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7608, d84781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16322 (p : Pattern) (ha : d7619 p = 1) (hb : d83662 p = 1) : d84788 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7615 q = 1) (hb : d77842 q = 1) : d7615 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7577 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7616 q = 1) (hb : d83662 q = 1) : d84785 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7616, d83662, d84785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7616, d83662, d84785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7617 q = 1) (hb : d83662 q = 1) : d84786 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7617, d84786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7617, d84786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7618 q = 1) (hb : d83662 q = 1) : d84787 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7618, d84787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7618, d84787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7619 q = 1) (hb : d83662 q = 1) : d84788 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7619, d84788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7619, d84788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16323 (p : Pattern) (ha : d83662 p = 1) (hb : d85511 p = 1) : d84794 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d806 q = 1) (hb : d83662 q = 1) : d806 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7602 q = 1) (hb : d83662 q = 1) : d84775 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7602, d84775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16320 q ha hb
    | true =>
      simp only [d7602, d84775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7603 q = 1) (hb : d83662 q = 1) : d84776 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7603, d84776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7603, d84776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7604 q = 1) (hb : d83662 q = 1) : d84777 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7604, d84777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7604, d84777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7605 q = 1) (hb : d83662 q = 1) : d84778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7605, d84778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7605, d84778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d83662 q = 1) : d816 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7609 q = 1) (hb : d83662 q = 1) : d84782 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7609, d84782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16321 q ha hb
    | true =>
      simp only [d7609, d84782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7610 q = 1) (hb : d83662 q = 1) : d84783 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7610, d84783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7610, d84783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7611 q = 1) (hb : d83662 q = 1) : d84784 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7611, d84784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7611, d84784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7620 q = 1) (hb : d83662 q = 1) : d84789 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7620, d84789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16322 q ha hb
    | true =>
      simp only [d7620, d84789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16315 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85507 q = 1) : d84790 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85507, d84790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85507, d84790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d7636 q = 1) (hb : d83662 q = 1) : d7636 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d85508 q = 1) : d84791 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85508, d84791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85508, d84791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85509 q = 1) : d84792 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85509, d84792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85509, d84792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d85510 q = 1) : d84793 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85510, d84793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85510, d84793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83662 q = 1) (hb : d85511 q = 1) : d84794 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85511, d84794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85511, d84794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro16324 (p : Pattern) (ha : d7641 p = 1) (hb : d83662 p = 1) : d84795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7577 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d775 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7578 q = 1) (hb : d83662 q = 1) : d7631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7578, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7579 q = 1) (hb : d83662 q = 1) : d7632 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7579, d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7600 q = 1) (hb : d83662 q = 1) : d84773 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7600, d84773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7600, d84773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7641 q = 1) (hb : d83662 q = 1) : d84795 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7641, d84795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7641, d84795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16325 (p : Pattern) (ha : d7646 p = 1) (hb : d83662 p = 1) : d84800 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7577 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d775 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7578 q = 1) (hb : d83662 q = 1) : d7631 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7578, d83662, d7631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7606 q = 1) (hb : d83662 q = 1) : d84779 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7606, d84779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7606, d84779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7607 q = 1) (hb : d83662 q = 1) : d84780 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7607, d84780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7607, d84780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7646 q = 1) (hb : d83662 q = 1) : d84800 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7646, d84800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7646, d84800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16326 (p : Pattern) (ha : d7650 p = 1) (hb : d83662 p = 1) : d84804 p = 1 := by
  have h0 (q : Pattern) (ha : d7615 q = 1) (hb : d77842 q = 1) : d7615 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7577 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7616 q = 1) (hb : d83662 q = 1) : d84785 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7616, d83662, d84785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7616, d83662, d84785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7617 q = 1) (hb : d83662 q = 1) : d84786 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7617, d84786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7617, d84786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7618 q = 1) (hb : d83662 q = 1) : d84787 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7618, d84787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7618, d84787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7650 q = 1) (hb : d83662 q = 1) : d84804 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7650, d84804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7650, d84804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16327 (p : Pattern) (ha : d83662 p = 1) (hb : d85516 p = 1) : d84810 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d806 q = 1) (hb : d83662 q = 1) : d806 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7602 q = 1) (hb : d83662 q = 1) : d84775 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7602, d84775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16320 q ha hb
    | true =>
      simp only [d7602, d84775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7603 q = 1) (hb : d83662 q = 1) : d84776 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7603, d84776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7603, d84776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7604 q = 1) (hb : d83662 q = 1) : d84777 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7604, d84777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7604, d84777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7605 q = 1) (hb : d83662 q = 1) : d84778 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7605, d84778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7605, d84778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d83662 q = 1) : d816 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7609 q = 1) (hb : d83662 q = 1) : d84782 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7609, d84782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16321 q ha hb
    | true =>
      simp only [d7609, d84782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7610 q = 1) (hb : d83662 q = 1) : d84783 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7610, d84783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7610, d84783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7611 q = 1) (hb : d83662 q = 1) : d84784 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7611, d84784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7611, d84784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7620 q = 1) (hb : d83662 q = 1) : d84789 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7620, d84789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16322 q ha hb
    | true =>
      simp only [d7620, d84789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16315 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85507 q = 1) : d84790 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85507, d84790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85507, d84790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d7636 q = 1) (hb : d83662 q = 1) : d7636 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d85508 q = 1) : d84791 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85508, d84791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85508, d84791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85509 q = 1) : d84792 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85509, d84792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85509, d84792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d85510 q = 1) : d84793 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85510, d84793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85510, d84793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d916 q = 1) (hb : d83662 q = 1) : d916 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d7642 q = 1) (hb : d83662 q = 1) : d84796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7642, d84796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16324 q ha hb
    | true =>
      simp only [d7642, d84796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7643 q = 1) (hb : d83662 q = 1) : d84797 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7643, d84797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7643, d84797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d7644 q = 1) (hb : d83662 q = 1) : d84798 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7644, d84798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d7644, d84798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d7645 q = 1) (hb : d83662 q = 1) : d84799 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7645, d84799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7645, d84799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d922 q = 1) (hb : d83662 q = 1) : d922 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d7647 q = 1) (hb : d83662 q = 1) : d84801 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7647, d84801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16325 q ha hb
    | true =>
      simp only [d7647, d84801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d7648 q = 1) (hb : d83662 q = 1) : d84802 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7648, d84802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7648, d84802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d7649 q = 1) (hb : d83662 q = 1) : d84803 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7649, d84803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d7649, d84803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d7651 q = 1) (hb : d83662 q = 1) : d84805 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7651, d84805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16326 q ha hb
    | true =>
      simp only [d7651, d84805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16317 q ha hb
  have h26 (q : Pattern) (ha : d83662 q = 1) (hb : d85512 q = 1) : d84806 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85512, d84806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d85512, d84806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d7657 q = 1) (hb : d83662 q = 1) : d7657 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d83662 q = 1) (hb : d85513 q = 1) : d84807 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85513, d84807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d85513, d84807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d83662 q = 1) (hb : d85514 q = 1) : d84808 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85514, d84808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d85514, d84808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d83662 q = 1) (hb : d85515 q = 1) : d84809 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85515, d84809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d85515, d84809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d83662 q = 1) (hb : d85516 q = 1) : d84810 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85516, d84810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85516, d84810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro16328 (p : Pattern) (ha : d83662 p = 1) (hb : d85523 p = 1) : d84819 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7651 q = 1) (hb : d83662 q = 1) : d84805 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7651, d84805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16326 q ha hb
    | true =>
      simp only [d7651, d84805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16317 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85512 q = 1) : d84806 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85512, d84806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85512, d84806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d7657 q = 1) (hb : d83662 q = 1) : d7657 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85513 q = 1) : d84807 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85513, d84807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85513, d84807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85521 q = 1) : d84817 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85521, d84817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85521, d84817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85522 q = 1) : d84818 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85522, d84818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85522, d84818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d85523 q = 1) : d84819 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85523, d84819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85523, d84819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16329 (p : Pattern) (ha : d7687 p = 1) (hb : d83662 p = 1) : d84828 p = 1 := by
  have h0 (q : Pattern) (ha : d7679 q = 1) (hb : d77842 q = 1) : d7679 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7683 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7684 q = 1) (hb : d83662 q = 1) : d84825 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7684, d83662, d84825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7684, d83662, d84825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7685 q = 1) (hb : d83662 q = 1) : d84826 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7685, d84826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7685, d84826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7686 q = 1) (hb : d83662 q = 1) : d84827 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7686, d84827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7686, d84827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7687 q = 1) (hb : d83662 q = 1) : d84828 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7687, d84828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7687, d84828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16330 (p : Pattern) (ha : d7691 p = 1) (hb : d83662 p = 1) : d7706 p = 1 := by
  have h0 (q : Pattern) (ha : d7683 q = 1) (hb : d77842 q = 1) : d7683 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1007 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7688 q = 1) (hb : d83662 q = 1) : d7703 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7688, d83662, d7703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7688, d83662, d7703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7689 q = 1) (hb : d83662 q = 1) : d7704 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7689, d7704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7689, d7704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7690 q = 1) (hb : d83662 q = 1) : d7705 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7690, d7705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7690, d7705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7691 q = 1) (hb : d83662 q = 1) : d7706 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7691, d7706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7691, d7706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16331 (p : Pattern) (ha : d83662 p = 1) (hb : d85533 p = 1) : d84834 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7692 q = 1) (hb : d83662 q = 1) : d84829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7692, d84829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16329 q ha hb
    | true =>
      simp only [d7692, d84829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16330 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85529 q = 1) : d84830 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85529, d84830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85529, d84830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d7708 q = 1) (hb : d83662 q = 1) : d7708 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85530 q = 1) : d84831 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85530, d84831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85530, d84831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85531 q = 1) : d84832 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85531, d84832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85531, d84832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85532 q = 1) : d84833 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85532, d84833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85532, d84833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d85533 q = 1) : d84834 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85533, d84834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85533, d84834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16332 (p : Pattern) (ha : d83662 p = 1) (hb : d85539 p = 1) : d84840 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7588 q = 1) (hb : d83662 q = 1) : d84762 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7588, d84762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7588, d84762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16316 q ha hb
  have h2 (q : Pattern) (ha : d7589 q = 1) (hb : d83662 q = 1) : d84763 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7589, d84763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7589, d84763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7597 q = 1) (hb : d83662 q = 1) : d84770 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7597, d84770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16316 q ha hb
    | true =>
      simp only [d7597, d84770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16318 q ha hb
  have h4 (q : Pattern) (ha : d7598 q = 1) (hb : d83662 q = 1) : d84771 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7598, d84771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7598, d84771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7599 q = 1) (hb : d83662 q = 1) : d84772 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7599, d84772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7599, d84772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85517 q = 1) : d84811 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85517, d84811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16323 q ha hb
    | true =>
      simp only [d85517, d84811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16327 q ha hb
  have h7 (q : Pattern) (ha : d950 q = 1) (hb : d83662 q = 1) : d950 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7664 q = 1) (hb : d83662 q = 1) : d84813 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7664, d84813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16319 q ha hb
    | true =>
      simp only [d7664, d84813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83662 q = 1) (hb : d85518 q = 1) : d84814 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85518, d84814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85518, d84814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d83662 q = 1) (hb : d85519 q = 1) : d84815 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85519, d84815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85519, d84815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85520 q = 1) : d84816 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85520, d84816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85520, d84816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d83662 q = 1) (hb : d85524 q = 1) : d84820 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85524, d84820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85524, d84820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16328 q ha hb
  have h13 (q : Pattern) (ha : d960 q = 1) (hb : d83662 q = 1) : d960 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85525 q = 1) : d84821 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85525, d84821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85525, d84821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d85526 q = 1) : d84822 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85526, d84822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85526, d84822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d83662 q = 1) (hb : d85527 q = 1) : d84823 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85527, d84823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85527, d84823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d83662 q = 1) (hb : d85528 q = 1) : d84824 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85528, d84824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85528, d84824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d83662 q = 1) (hb : d85534 q = 1) : d84835 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85534, d84835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85534, d84835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16331 q ha hb
  have h19 (q : Pattern) (ha : d1070 q = 1) (hb : d83662 q = 1) : d1070 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d83662 q = 1) (hb : d85535 q = 1) : d84836 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85535, d84836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85535, d84836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d83662 q = 1) (hb : d85536 q = 1) : d84837 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85536, d84837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85536, d84837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d83662 q = 1) (hb : d85537 q = 1) : d84838 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85537, d84838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85537, d84838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83662 q = 1) (hb : d85538 q = 1) : d84839 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85538, d84839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85538, d84839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d83662 q = 1) (hb : d85539 q = 1) : d84840 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85539, d84840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85539, d84840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro16333 (p : Pattern) (ha : d83662 p = 1) (hb : d85545 p = 1) : d84846 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d85540 q = 1) : d84841 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85540, d84841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85540, d84841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16332 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85541 q = 1) : d84842 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85541, d84842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85541, d84842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d85542 q = 1) : d84843 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85542, d84843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85542, d84843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85543 q = 1) : d84844 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85543, d84844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85543, d84844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85544 q = 1) : d84845 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85544, d84845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85544, d84845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85545 q = 1) : d84846 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85545, d84846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85545, d84846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16334 (p : Pattern) (ha : d7734 p = 1) (hb : d83662 p = 1) : d7787 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7730 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7731 q = 1) (hb : d83662 q = 1) : d7784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7731, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7732 q = 1) (hb : d83662 q = 1) : d7785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7732, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7733 q = 1) (hb : d83662 q = 1) : d7786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7733, d7786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7733, d7786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7734 q = 1) (hb : d83662 q = 1) : d7787 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7734, d7787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7734, d7787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16335 (p : Pattern) (ha : d7740 p = 1) (hb : d83662 p = 1) : d84854 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d83662 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7735 q = 1) (hb : d83662 q = 1) : d84849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d84849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16334 q ha hb
    | true =>
      simp only [d7735, d84849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7736 q = 1) (hb : d83662 q = 1) : d84850 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d84850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d84850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7737 q = 1) (hb : d83662 q = 1) : d84851 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d84851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7737, d84851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7738 q = 1) (hb : d83662 q = 1) : d84852 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d84852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d84852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7739 q = 1) (hb : d83662 q = 1) : d84853 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d84853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d84853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7740 q = 1) (hb : d83662 q = 1) : d84854 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7740, d84854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7740, d84854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16336 (p : Pattern) (ha : d7743 p = 1) (hb : d83662 p = 1) : d7808 p = 1 := by
  have h0 (q : Pattern) (ha : d7730 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1154 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7731 q = 1) (hb : d83662 q = 1) : d7784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7731, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7732 q = 1) (hb : d83662 q = 1) : d7785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7732, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7733 q = 1) (hb : d83662 q = 1) : d7786 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7733, d7786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7733, d7786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7743 q = 1) (hb : d83662 q = 1) : d7808 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7743, d7808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7743, d7808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16337 (p : Pattern) (ha : d7749 p = 1) (hb : d83662 p = 1) : d84862 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d83662 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7735 q = 1) (hb : d83662 q = 1) : d84849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d84849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16334 q ha hb
    | true =>
      simp only [d7735, d84849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7736 q = 1) (hb : d83662 q = 1) : d84850 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d84850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d84850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7737 q = 1) (hb : d83662 q = 1) : d84851 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d84851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7737, d84851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7738 q = 1) (hb : d83662 q = 1) : d84852 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d84852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d84852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7739 q = 1) (hb : d83662 q = 1) : d84853 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d84853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d84853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1172 q = 1) (hb : d83662 q = 1) : d1172 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7744 q = 1) (hb : d83662 q = 1) : d84857 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7744, d84857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16336 q ha hb
    | true =>
      simp only [d7744, d84857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7745 q = 1) (hb : d83662 q = 1) : d84858 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, d84858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7745, d84858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7746 q = 1) (hb : d83662 q = 1) : d84859 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, d84859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7746, d84859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7747 q = 1) (hb : d83662 q = 1) : d84860 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, d84860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7747, d84860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d7748 q = 1) (hb : d83662 q = 1) : d84861 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, d84861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7748, d84861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7749 q = 1) (hb : d83662 q = 1) : d84862 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7749, d84862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7749, d84862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16338 (p : Pattern) (ha : d7816 p = 1) (hb : d83662 p = 1) : d84905 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1162 q = 1) (hb : d83662 q = 1) : d1162 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7735 q = 1) (hb : d83662 q = 1) : d84849 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7735, d84849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16334 q ha hb
    | true =>
      simp only [d7735, d84849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7736 q = 1) (hb : d83662 q = 1) : d84850 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7736, d84850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7736, d84850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7737 q = 1) (hb : d83662 q = 1) : d84851 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7737, d84851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7737, d84851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7738 q = 1) (hb : d83662 q = 1) : d84852 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7738, d84852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7738, d84852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7739 q = 1) (hb : d83662 q = 1) : d84853 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7739, d84853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7739, d84853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1354 q = 1) (hb : d83662 q = 1) : d1354 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7816 q = 1) (hb : d83662 q = 1) : d84905 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7816, d84905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7816, d84905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16339 (p : Pattern) (ha : d7754 p = 1) (hb : d83662 p = 1) : d84867 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7730 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7731 q = 1) (hb : d83662 q = 1) : d7784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7731, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7732 q = 1) (hb : d83662 q = 1) : d7785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7732, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7753 q = 1) (hb : d83662 q = 1) : d84866 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7753, d84866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7753, d84866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7754 q = 1) (hb : d83662 q = 1) : d84867 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7754, d84867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7754, d84867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16340 (p : Pattern) (ha : d7761 p = 1) (hb : d83662 p = 1) : d84874 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7730 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7731 q = 1) (hb : d83662 q = 1) : d7784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7731, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7759 q = 1) (hb : d83662 q = 1) : d84872 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7759, d84872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7759, d84872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7760 q = 1) (hb : d83662 q = 1) : d84873 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7760, d84873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7760, d84873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7761 q = 1) (hb : d83662 q = 1) : d84874 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7761, d84874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7761, d84874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16341 (p : Pattern) (ha : d7772 p = 1) (hb : d83662 p = 1) : d84881 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7768 q = 1) (hb : d77842 q = 1) : d7768 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7730 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7769 q = 1) (hb : d83662 q = 1) : d84878 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7769, d83662, d84878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7769, d83662, d84878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7770 q = 1) (hb : d83662 q = 1) : d84879 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7770, d84879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7770, d84879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7771 q = 1) (hb : d83662 q = 1) : d84880 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7771, d84880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7771, d84880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7772 q = 1) (hb : d83662 q = 1) : d84881 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7772, d84881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7772, d84881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16342 (p : Pattern) (ha : d83662 p = 1) (hb : d85552 p = 1) : d84887 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1185 q = 1) (hb : d83662 q = 1) : d1185 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7755 q = 1) (hb : d83662 q = 1) : d84868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7755, d84868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16339 q ha hb
    | true =>
      simp only [d7755, d84868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7756 q = 1) (hb : d83662 q = 1) : d84869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7756, d84869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7756, d84869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7757 q = 1) (hb : d83662 q = 1) : d84870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7757, d84870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7757, d84870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7758 q = 1) (hb : d83662 q = 1) : d84871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7758, d84871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7758, d84871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d83662 q = 1) : d1195 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7762 q = 1) (hb : d83662 q = 1) : d84875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7762, d84875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16340 q ha hb
    | true =>
      simp only [d7762, d84875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7763 q = 1) (hb : d83662 q = 1) : d84876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7763, d84876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7763, d84876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7764 q = 1) (hb : d83662 q = 1) : d84877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7764, d84877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7764, d84877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7773 q = 1) (hb : d83662 q = 1) : d84882 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7773, d84882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16341 q ha hb
    | true =>
      simp only [d7773, d84882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16334 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85548 q = 1) : d84883 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85548, d84883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85548, d84883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d7789 q = 1) (hb : d83662 q = 1) : d7789 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d85549 q = 1) : d84884 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85549, d84884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85549, d84884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85550 q = 1) : d84885 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85550, d84885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85550, d84885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d85551 q = 1) : d84886 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85551, d84886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85551, d84886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83662 q = 1) (hb : d85552 q = 1) : d84887 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85552, d84887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85552, d84887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro16343 (p : Pattern) (ha : d7794 p = 1) (hb : d83662 p = 1) : d84888 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7730 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7731 q = 1) (hb : d83662 q = 1) : d7784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7731, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7732 q = 1) (hb : d83662 q = 1) : d7785 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7732, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7732, d7785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7753 q = 1) (hb : d83662 q = 1) : d84866 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7753, d84866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7753, d84866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7794 q = 1) (hb : d83662 q = 1) : d84888 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7794, d84888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7794, d84888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16344 (p : Pattern) (ha : d7799 p = 1) (hb : d83662 p = 1) : d84893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7730 q = 1) (hb : d77842 q = 1) : d7730 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1154 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7731 q = 1) (hb : d83662 q = 1) : d7784 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7731, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7731, d83662, d7784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7759 q = 1) (hb : d83662 q = 1) : d84872 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7759, d84872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7759, d84872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7760 q = 1) (hb : d83662 q = 1) : d84873 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7760, d84873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7760, d84873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7799 q = 1) (hb : d83662 q = 1) : d84893 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7799, d84893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7799, d84893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16345 (p : Pattern) (ha : d7803 p = 1) (hb : d83662 p = 1) : d84897 p = 1 := by
  have h0 (q : Pattern) (ha : d7768 q = 1) (hb : d77842 q = 1) : d7768 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7730 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7769 q = 1) (hb : d83662 q = 1) : d84878 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7769, d83662, d84878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7769, d83662, d84878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7770 q = 1) (hb : d83662 q = 1) : d84879 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7770, d84879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7770, d84879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7771 q = 1) (hb : d83662 q = 1) : d84880 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7771, d84880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7771, d84880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7803 q = 1) (hb : d83662 q = 1) : d84897 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7803, d84897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7803, d84897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16346 (p : Pattern) (ha : d83662 p = 1) (hb : d85557 p = 1) : d84903 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1185 q = 1) (hb : d83662 q = 1) : d1185 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7755 q = 1) (hb : d83662 q = 1) : d84868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7755, d84868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16339 q ha hb
    | true =>
      simp only [d7755, d84868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7756 q = 1) (hb : d83662 q = 1) : d84869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7756, d84869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7756, d84869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7757 q = 1) (hb : d83662 q = 1) : d84870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7757, d84870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7757, d84870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7758 q = 1) (hb : d83662 q = 1) : d84871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7758, d84871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7758, d84871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d83662 q = 1) : d1195 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7762 q = 1) (hb : d83662 q = 1) : d84875 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7762, d84875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16340 q ha hb
    | true =>
      simp only [d7762, d84875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7763 q = 1) (hb : d83662 q = 1) : d84876 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7763, d84876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7763, d84876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7764 q = 1) (hb : d83662 q = 1) : d84877 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7764, d84877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7764, d84877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7773 q = 1) (hb : d83662 q = 1) : d84882 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7773, d84882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16341 q ha hb
    | true =>
      simp only [d7773, d84882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16334 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85548 q = 1) : d84883 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85548, d84883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85548, d84883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d7789 q = 1) (hb : d83662 q = 1) : d7789 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d85549 q = 1) : d84884 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85549, d84884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85549, d84884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85550 q = 1) : d84885 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85550, d84885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85550, d84885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d85551 q = 1) : d84886 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85551, d84886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85551, d84886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1327 q = 1) (hb : d83662 q = 1) : d1327 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d7795 q = 1) (hb : d83662 q = 1) : d84889 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7795, d84889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16343 q ha hb
    | true =>
      simp only [d7795, d84889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7796 q = 1) (hb : d83662 q = 1) : d84890 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7796, d84890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7796, d84890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d7797 q = 1) (hb : d83662 q = 1) : d84891 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7797, d84891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d7797, d84891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d7798 q = 1) (hb : d83662 q = 1) : d84892 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7798, d84892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7798, d84892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d1333 q = 1) (hb : d83662 q = 1) : d1333 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d7800 q = 1) (hb : d83662 q = 1) : d84894 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7800, d84894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16344 q ha hb
    | true =>
      simp only [d7800, d84894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d7801 q = 1) (hb : d83662 q = 1) : d84895 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7801, d84895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7801, d84895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d7802 q = 1) (hb : d83662 q = 1) : d84896 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7802, d84896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d7802, d84896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d7804 q = 1) (hb : d83662 q = 1) : d84898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7804, d84898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16345 q ha hb
    | true =>
      simp only [d7804, d84898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16336 q ha hb
  have h26 (q : Pattern) (ha : d83662 q = 1) (hb : d85553 q = 1) : d84899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85553, d84899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d85553, d84899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d7810 q = 1) (hb : d83662 q = 1) : d7810 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d83662 q = 1) (hb : d85554 q = 1) : d84900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85554, d84900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d85554, d84900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d83662 q = 1) (hb : d85555 q = 1) : d84901 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85555, d84901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d85555, d84901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d83662 q = 1) (hb : d85556 q = 1) : d84902 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85556, d84902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d85556, d84902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d83662 q = 1) (hb : d85557 q = 1) : d84903 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85557, d84903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85557, d84903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro16347 (p : Pattern) (ha : d83662 p = 1) (hb : d85564 p = 1) : d84912 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7804 q = 1) (hb : d83662 q = 1) : d84898 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7804, d84898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16345 q ha hb
    | true =>
      simp only [d7804, d84898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16336 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85553 q = 1) : d84899 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85553, d84899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85553, d84899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d7810 q = 1) (hb : d83662 q = 1) : d7810 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85554 q = 1) : d84900 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85554, d84900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85554, d84900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85562 q = 1) : d84910 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85562, d84910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85562, d84910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85563 q = 1) : d84911 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85563, d84911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85563, d84911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d85564 q = 1) : d84912 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85564, d84912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85564, d84912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16348 (p : Pattern) (ha : d7840 p = 1) (hb : d83662 p = 1) : d84921 p = 1 := by
  have h0 (q : Pattern) (ha : d7832 q = 1) (hb : d77842 q = 1) : d7832 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7836 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7837 q = 1) (hb : d83662 q = 1) : d84918 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7837, d83662, d84918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7837, d83662, d84918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7838 q = 1) (hb : d83662 q = 1) : d84919 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7838, d84919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7838, d84919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7839 q = 1) (hb : d83662 q = 1) : d84920 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7839, d84920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7839, d84920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7840 q = 1) (hb : d83662 q = 1) : d84921 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7840, d84921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7840, d84921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16349 (p : Pattern) (ha : d7844 p = 1) (hb : d83662 p = 1) : d7859 p = 1 := by
  have h0 (q : Pattern) (ha : d7836 q = 1) (hb : d77842 q = 1) : d7836 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1432 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7841 q = 1) (hb : d83662 q = 1) : d7856 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7841, d83662, d7856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7841, d83662, d7856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7842 q = 1) (hb : d83662 q = 1) : d7857 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7842, d7857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7842, d7857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7843 q = 1) (hb : d83662 q = 1) : d7858 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7843, d7858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7843, d7858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7844 q = 1) (hb : d83662 q = 1) : d7859 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7844, d7859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7844, d7859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16350 (p : Pattern) (ha : d83662 p = 1) (hb : d85574 p = 1) : d84927 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7845 q = 1) (hb : d83662 q = 1) : d84922 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7845, d84922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16348 q ha hb
    | true =>
      simp only [d7845, d84922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16349 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85570 q = 1) : d84923 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85570, d84923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85570, d84923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d7861 q = 1) (hb : d83662 q = 1) : d7861 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85571 q = 1) : d84924 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85571, d84924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85571, d84924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85572 q = 1) : d84925 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85572, d84925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85572, d84925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85573 q = 1) : d84926 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85573, d84926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85573, d84926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d85574 q = 1) : d84927 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85574, d84927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85574, d84927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16351 (p : Pattern) (ha : d83662 p = 1) (hb : d85580 p = 1) : d84933 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7741 q = 1) (hb : d83662 q = 1) : d84855 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7741, d84855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7741, d84855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16335 q ha hb
  have h2 (q : Pattern) (ha : d7742 q = 1) (hb : d83662 q = 1) : d84856 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7742, d84856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7742, d84856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7750 q = 1) (hb : d83662 q = 1) : d84863 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7750, d84863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16335 q ha hb
    | true =>
      simp only [d7750, d84863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16337 q ha hb
  have h4 (q : Pattern) (ha : d7751 q = 1) (hb : d83662 q = 1) : d84864 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7751, d84864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7751, d84864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7752 q = 1) (hb : d83662 q = 1) : d84865 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7752, d84865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7752, d84865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85558 q = 1) : d84904 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85558, d84904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16342 q ha hb
    | true =>
      simp only [d85558, d84904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16346 q ha hb
  have h7 (q : Pattern) (ha : d1361 q = 1) (hb : d83662 q = 1) : d1361 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7817 q = 1) (hb : d83662 q = 1) : d84906 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7817, d84906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16338 q ha hb
    | true =>
      simp only [d7817, d84906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83662 q = 1) (hb : d85559 q = 1) : d84907 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85559, d84907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85559, d84907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d83662 q = 1) (hb : d85560 q = 1) : d84908 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85560, d84908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85560, d84908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85561 q = 1) : d84909 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85561, d84909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85561, d84909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d83662 q = 1) (hb : d85565 q = 1) : d84913 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85565, d84913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85565, d84913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16347 q ha hb
  have h13 (q : Pattern) (ha : d1371 q = 1) (hb : d83662 q = 1) : d1371 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85566 q = 1) : d84914 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85566, d84914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85566, d84914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d85567 q = 1) : d84915 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85567, d84915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85567, d84915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d83662 q = 1) (hb : d85568 q = 1) : d84916 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85568, d84916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85568, d84916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d83662 q = 1) (hb : d85569 q = 1) : d84917 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85569, d84917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85569, d84917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d83662 q = 1) (hb : d85575 q = 1) : d84928 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85575, d84928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85575, d84928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16350 q ha hb
  have h19 (q : Pattern) (ha : d1504 q = 1) (hb : d83662 q = 1) : d1504 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d83662 q = 1) (hb : d85576 q = 1) : d84929 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85576, d84929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85576, d84929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d83662 q = 1) (hb : d85577 q = 1) : d84930 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85577, d84930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85577, d84930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d83662 q = 1) (hb : d85578 q = 1) : d84931 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85578, d84931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85578, d84931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83662 q = 1) (hb : d85579 q = 1) : d84932 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85579, d84932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85579, d84932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d83662 q = 1) (hb : d85580 q = 1) : d84933 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85580, d84933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85580, d84933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro16352 (p : Pattern) (ha : d83662 p = 1) (hb : d85586 p = 1) : d84939 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d85581 q = 1) : d84934 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85581, d84934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85581, d84934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16351 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85582 q = 1) : d84935 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85582, d84935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85582, d84935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d85583 q = 1) : d84936 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85583, d84936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85583, d84936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85584 q = 1) : d84937 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85584, d84937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85584, d84937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85585 q = 1) : d84938 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85585, d84938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85585, d84938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85586 q = 1) : d84939 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85586, d84939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85586, d84939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16353 (p : Pattern) (ha : d7888 p = 1) (hb : d83662 p = 1) : d7941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7884 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1615 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7885 q = 1) (hb : d83662 q = 1) : d7938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7885, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7886 q = 1) (hb : d83662 q = 1) : d7939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7886, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7887 q = 1) (hb : d83662 q = 1) : d7940 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7887, d7940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7887, d7940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7888 q = 1) (hb : d83662 q = 1) : d7941 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7888, d7941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7888, d7941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16354 (p : Pattern) (ha : d7894 p = 1) (hb : d83662 p = 1) : d84948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d83662 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7889 q = 1) (hb : d83662 q = 1) : d84943 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d84943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16353 q ha hb
    | true =>
      simp only [d7889, d84943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7890 q = 1) (hb : d83662 q = 1) : d84944 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d84944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d84944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7891 q = 1) (hb : d83662 q = 1) : d84945 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d84945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7891, d84945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7892 q = 1) (hb : d83662 q = 1) : d84946 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d84946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d84946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7893 q = 1) (hb : d83662 q = 1) : d84947 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d84947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d84947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7894 q = 1) (hb : d83662 q = 1) : d84948 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7894, d84948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7894, d84948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16355 (p : Pattern) (ha : d7897 p = 1) (hb : d83662 p = 1) : d7962 p = 1 := by
  have h0 (q : Pattern) (ha : d7884 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1615 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7885 q = 1) (hb : d83662 q = 1) : d7938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7885, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7886 q = 1) (hb : d83662 q = 1) : d7939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7886, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7887 q = 1) (hb : d83662 q = 1) : d7940 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7887, d7940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7887, d7940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7897 q = 1) (hb : d83662 q = 1) : d7962 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7897, d7962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7897, d7962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16356 (p : Pattern) (ha : d7903 p = 1) (hb : d83662 p = 1) : d84956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d83662 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7889 q = 1) (hb : d83662 q = 1) : d84943 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d84943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16353 q ha hb
    | true =>
      simp only [d7889, d84943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7890 q = 1) (hb : d83662 q = 1) : d84944 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d84944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d84944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7891 q = 1) (hb : d83662 q = 1) : d84945 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d84945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7891, d84945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7892 q = 1) (hb : d83662 q = 1) : d84946 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d84946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d84946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7893 q = 1) (hb : d83662 q = 1) : d84947 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d84947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d84947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1633 q = 1) (hb : d83662 q = 1) : d1633 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7898 q = 1) (hb : d83662 q = 1) : d84951 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7898, d84951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16355 q ha hb
    | true =>
      simp only [d7898, d84951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7899 q = 1) (hb : d83662 q = 1) : d84952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, d84952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7899, d84952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7900 q = 1) (hb : d83662 q = 1) : d84953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, d84953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7900, d84953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7901 q = 1) (hb : d83662 q = 1) : d84954 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, d84954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7901, d84954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d7902 q = 1) (hb : d83662 q = 1) : d84955 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, d84955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7902, d84955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7903 q = 1) (hb : d83662 q = 1) : d84956 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7903, d84956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7903, d84956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16357 (p : Pattern) (ha : d7970 p = 1) (hb : d83662 p = 1) : d84999 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1623 q = 1) (hb : d83662 q = 1) : d1623 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7889 q = 1) (hb : d83662 q = 1) : d84943 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7889, d84943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16353 q ha hb
    | true =>
      simp only [d7889, d84943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7890 q = 1) (hb : d83662 q = 1) : d84944 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7890, d84944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7890, d84944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7891 q = 1) (hb : d83662 q = 1) : d84945 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7891, d84945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7891, d84945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7892 q = 1) (hb : d83662 q = 1) : d84946 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7892, d84946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7892, d84946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7893 q = 1) (hb : d83662 q = 1) : d84947 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7893, d84947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7893, d84947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1831 q = 1) (hb : d83662 q = 1) : d1831 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7970 q = 1) (hb : d83662 q = 1) : d84999 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7970, d84999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7970, d84999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16358 (p : Pattern) (ha : d7908 p = 1) (hb : d83662 p = 1) : d84961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7884 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1615 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7885 q = 1) (hb : d83662 q = 1) : d7938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7885, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7886 q = 1) (hb : d83662 q = 1) : d7939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7886, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7907 q = 1) (hb : d83662 q = 1) : d84960 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7907, d84960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7907, d84960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7908 q = 1) (hb : d83662 q = 1) : d84961 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7908, d84961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7908, d84961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16359 (p : Pattern) (ha : d7915 p = 1) (hb : d83662 p = 1) : d84968 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7884 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1615 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7885 q = 1) (hb : d83662 q = 1) : d7938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7885, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7913 q = 1) (hb : d83662 q = 1) : d84966 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7913, d84966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7913, d84966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7914 q = 1) (hb : d83662 q = 1) : d84967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7914, d84967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7914, d84967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7915 q = 1) (hb : d83662 q = 1) : d84968 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7915, d84968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7915, d84968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16360 (p : Pattern) (ha : d7926 p = 1) (hb : d83662 p = 1) : d84975 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7922 q = 1) (hb : d77842 q = 1) : d7922 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d7884 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7923 q = 1) (hb : d83662 q = 1) : d84972 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7923, d83662, d84972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7923, d83662, d84972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7924 q = 1) (hb : d83662 q = 1) : d84973 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7924, d84973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7924, d84973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7925 q = 1) (hb : d83662 q = 1) : d84974 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7925, d84974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7925, d84974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7926 q = 1) (hb : d83662 q = 1) : d84975 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7926, d84975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7926, d84975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16361 (p : Pattern) (ha : d83662 p = 1) (hb : d85594 p = 1) : d84981 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1646 q = 1) (hb : d83662 q = 1) : d1646 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7909 q = 1) (hb : d83662 q = 1) : d84962 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7909, d84962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16358 q ha hb
    | true =>
      simp only [d7909, d84962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7910 q = 1) (hb : d83662 q = 1) : d84963 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7910, d84963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7910, d84963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7911 q = 1) (hb : d83662 q = 1) : d84964 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7911, d84964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7911, d84964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7912 q = 1) (hb : d83662 q = 1) : d84965 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7912, d84965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7912, d84965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d83662 q = 1) : d1656 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7916 q = 1) (hb : d83662 q = 1) : d84969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7916, d84969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16359 q ha hb
    | true =>
      simp only [d7916, d84969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7917 q = 1) (hb : d83662 q = 1) : d84970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7917, d84970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7917, d84970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7918 q = 1) (hb : d83662 q = 1) : d84971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7918, d84971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7918, d84971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7927 q = 1) (hb : d83662 q = 1) : d84976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7927, d84976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16360 q ha hb
    | true =>
      simp only [d7927, d84976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16353 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85590 q = 1) : d84977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85590, d84977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85590, d84977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d7943 q = 1) (hb : d83662 q = 1) : d7943 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d85591 q = 1) : d84978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85591, d84978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85591, d84978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85592 q = 1) : d84979 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85592, d84979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85592, d84979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d85593 q = 1) : d84980 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85593, d84980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85593, d84980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83662 q = 1) (hb : d85594 q = 1) : d84981 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85594, d84981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85594, d84981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro16362 (p : Pattern) (ha : d7948 p = 1) (hb : d83662 p = 1) : d84982 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7884 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1615 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7885 q = 1) (hb : d83662 q = 1) : d7938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7885, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7886 q = 1) (hb : d83662 q = 1) : d7939 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7886, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7886, d7939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7907 q = 1) (hb : d83662 q = 1) : d84960 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7907, d84960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7907, d84960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7948 q = 1) (hb : d83662 q = 1) : d84982 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7948, d84982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7948, d84982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16363 (p : Pattern) (ha : d7953 p = 1) (hb : d83662 p = 1) : d84987 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7884 q = 1) (hb : d77842 q = 1) : d7884 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1615 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7885 q = 1) (hb : d83662 q = 1) : d7938 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7885, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7885, d83662, d7938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d7913 q = 1) (hb : d83662 q = 1) : d84966 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7913, d84966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7913, d84966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7914 q = 1) (hb : d83662 q = 1) : d84967 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7914, d84967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7914, d84967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7953 q = 1) (hb : d83662 q = 1) : d84987 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7953, d84987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7953, d84987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16364 (p : Pattern) (ha : d7957 p = 1) (hb : d83662 p = 1) : d84991 p = 1 := by
  have h0 (q : Pattern) (ha : d7922 q = 1) (hb : d77842 q = 1) : d7922 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7884 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7923 q = 1) (hb : d83662 q = 1) : d84972 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7923, d83662, d84972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7923, d83662, d84972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7924 q = 1) (hb : d83662 q = 1) : d84973 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7924, d84973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7924, d84973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7925 q = 1) (hb : d83662 q = 1) : d84974 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7925, d84974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7925, d84974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7957 q = 1) (hb : d83662 q = 1) : d84991 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7957, d84991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7957, d84991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16365 (p : Pattern) (ha : d83662 p = 1) (hb : d85599 p = 1) : d84997 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1646 q = 1) (hb : d83662 q = 1) : d1646 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7909 q = 1) (hb : d83662 q = 1) : d84962 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7909, d84962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16358 q ha hb
    | true =>
      simp only [d7909, d84962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7910 q = 1) (hb : d83662 q = 1) : d84963 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7910, d84963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7910, d84963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7911 q = 1) (hb : d83662 q = 1) : d84964 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7911, d84964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7911, d84964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7912 q = 1) (hb : d83662 q = 1) : d84965 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7912, d84965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7912, d84965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d83662 q = 1) : d1656 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7916 q = 1) (hb : d83662 q = 1) : d84969 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7916, d84969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16359 q ha hb
    | true =>
      simp only [d7916, d84969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d7917 q = 1) (hb : d83662 q = 1) : d84970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7917, d84970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7917, d84970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7918 q = 1) (hb : d83662 q = 1) : d84971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7918, d84971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7918, d84971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d7927 q = 1) (hb : d83662 q = 1) : d84976 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7927, d84976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16360 q ha hb
    | true =>
      simp only [d7927, d84976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16353 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85590 q = 1) : d84977 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85590, d84977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85590, d84977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d7943 q = 1) (hb : d83662 q = 1) : d7943 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d85591 q = 1) : d84978 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85591, d84978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85591, d84978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85592 q = 1) : d84979 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85592, d84979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85592, d84979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d85593 q = 1) : d84980 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85593, d84980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85593, d84980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1804 q = 1) (hb : d83662 q = 1) : d1804 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d7949 q = 1) (hb : d83662 q = 1) : d84983 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7949, d84983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16362 q ha hb
    | true =>
      simp only [d7949, d84983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d7950 q = 1) (hb : d83662 q = 1) : d84984 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7950, d84984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7950, d84984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d7951 q = 1) (hb : d83662 q = 1) : d84985 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7951, d84985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d7951, d84985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d7952 q = 1) (hb : d83662 q = 1) : d84986 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7952, d84986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7952, d84986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d1810 q = 1) (hb : d83662 q = 1) : d1810 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d7954 q = 1) (hb : d83662 q = 1) : d84988 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7954, d84988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16363 q ha hb
    | true =>
      simp only [d7954, d84988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d7955 q = 1) (hb : d83662 q = 1) : d84989 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7955, d84989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7955, d84989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d7956 q = 1) (hb : d83662 q = 1) : d84990 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7956, d84990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d7956, d84990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d7958 q = 1) (hb : d83662 q = 1) : d84992 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7958, d84992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16364 q ha hb
    | true =>
      simp only [d7958, d84992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16355 q ha hb
  have h26 (q : Pattern) (ha : d83662 q = 1) (hb : d85595 q = 1) : d84993 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85595, d84993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d85595, d84993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d7964 q = 1) (hb : d83662 q = 1) : d7964 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d83662 q = 1) (hb : d85596 q = 1) : d84994 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85596, d84994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d85596, d84994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d83662 q = 1) (hb : d85597 q = 1) : d84995 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85597, d84995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d85597, d84995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d83662 q = 1) (hb : d85598 q = 1) : d84996 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85598, d84996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d85598, d84996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d83662 q = 1) (hb : d85599 q = 1) : d84997 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85599, d84997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85599, d84997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro16366 (p : Pattern) (ha : d83662 p = 1) (hb : d85606 p = 1) : d85006 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7958 q = 1) (hb : d83662 q = 1) : d84992 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7958, d84992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16364 q ha hb
    | true =>
      simp only [d7958, d84992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16355 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85595 q = 1) : d84993 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85595, d84993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85595, d84993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d7964 q = 1) (hb : d83662 q = 1) : d7964 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85596 q = 1) : d84994 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85596, d84994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85596, d84994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85604 q = 1) : d85004 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85604, d85004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85604, d85004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85605 q = 1) : d85005 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85605, d85005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85605, d85005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d85606 q = 1) : d85006 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85606, d85006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85606, d85006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16367 (p : Pattern) (ha : d7994 p = 1) (hb : d83662 p = 1) : d85015 p = 1 := by
  have h0 (q : Pattern) (ha : d7986 q = 1) (hb : d77842 q = 1) : d7986 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7990 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7991 q = 1) (hb : d83662 q = 1) : d85012 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7991, d83662, d85012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7991, d83662, d85012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7992 q = 1) (hb : d83662 q = 1) : d85013 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7992, d85013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7992, d85013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7993 q = 1) (hb : d83662 q = 1) : d85014 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7993, d85014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7993, d85014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7994 q = 1) (hb : d83662 q = 1) : d85015 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7994, d85015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7994, d85015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16368 (p : Pattern) (ha : d7998 p = 1) (hb : d83662 p = 1) : d8013 p = 1 := by
  have h0 (q : Pattern) (ha : d7990 q = 1) (hb : d77842 q = 1) : d7990 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1909 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7995 q = 1) (hb : d83662 q = 1) : d8010 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7995, d83662, d8010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7995, d83662, d8010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7996 q = 1) (hb : d83662 q = 1) : d8011 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7996, d8011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7996, d8011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7997 q = 1) (hb : d83662 q = 1) : d8012 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7997, d8012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7997, d8012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7998 q = 1) (hb : d83662 q = 1) : d8013 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7998, d8013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7998, d8013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16369 (p : Pattern) (ha : d83662 p = 1) (hb : d85616 p = 1) : d85021 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7999 q = 1) (hb : d83662 q = 1) : d85016 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7999, d85016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16367 q ha hb
    | true =>
      simp only [d7999, d85016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16368 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85612 q = 1) : d85017 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85612, d85017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85612, d85017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d8015 q = 1) (hb : d83662 q = 1) : d8015 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85613 q = 1) : d85018 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85613, d85018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85613, d85018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85614 q = 1) : d85019 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85614, d85019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85614, d85019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85615 q = 1) : d85020 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85615, d85020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85615, d85020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d85616 q = 1) : d85021 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85616, d85021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85616, d85021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16370 (p : Pattern) (ha : d83662 p = 1) (hb : d85622 p = 1) : d85027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7895 q = 1) (hb : d83662 q = 1) : d84949 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7895, d84949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7895, d84949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16354 q ha hb
  have h2 (q : Pattern) (ha : d7896 q = 1) (hb : d83662 q = 1) : d84950 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7896, d84950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7896, d84950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7904 q = 1) (hb : d83662 q = 1) : d84957 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7904, d84957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16354 q ha hb
    | true =>
      simp only [d7904, d84957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16356 q ha hb
  have h4 (q : Pattern) (ha : d7905 q = 1) (hb : d83662 q = 1) : d84958 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7905, d84958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7905, d84958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7906 q = 1) (hb : d83662 q = 1) : d84959 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7906, d84959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7906, d84959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85600 q = 1) : d84998 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85600, d84998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16361 q ha hb
    | true =>
      simp only [d85600, d84998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16365 q ha hb
  have h7 (q : Pattern) (ha : d1838 q = 1) (hb : d83662 q = 1) : d1838 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7971 q = 1) (hb : d83662 q = 1) : d85000 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7971, d85000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16357 q ha hb
    | true =>
      simp only [d7971, d85000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83662 q = 1) (hb : d85601 q = 1) : d85001 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85601, d85001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85601, d85001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d83662 q = 1) (hb : d85602 q = 1) : d85002 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85602, d85002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85602, d85002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85603 q = 1) : d85003 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85603, d85003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85603, d85003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d83662 q = 1) (hb : d85607 q = 1) : d85007 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85607, d85007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85607, d85007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16366 q ha hb
  have h13 (q : Pattern) (ha : d1848 q = 1) (hb : d83662 q = 1) : d1848 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85608 q = 1) : d85008 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85608, d85008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85608, d85008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d85609 q = 1) : d85009 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85609, d85009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85609, d85009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d83662 q = 1) (hb : d85610 q = 1) : d85010 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85610, d85010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85610, d85010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d83662 q = 1) (hb : d85611 q = 1) : d85011 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85611, d85011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85611, d85011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d83662 q = 1) (hb : d85617 q = 1) : d85022 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85617, d85022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85617, d85022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16369 q ha hb
  have h19 (q : Pattern) (ha : d1981 q = 1) (hb : d83662 q = 1) : d1981 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d83662 q = 1) (hb : d85618 q = 1) : d85023 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85618, d85023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85618, d85023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d83662 q = 1) (hb : d85619 q = 1) : d85024 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85619, d85024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85619, d85024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d83662 q = 1) (hb : d85620 q = 1) : d85025 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85620, d85025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85620, d85025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83662 q = 1) (hb : d85621 q = 1) : d85026 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85621, d85026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85621, d85026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d83662 q = 1) (hb : d85622 q = 1) : d85027 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85622, d85027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85622, d85027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro16371 (p : Pattern) (ha : d83662 p = 1) (hb : d85628 p = 1) : d85033 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d85623 q = 1) : d85028 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85623, d85028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85623, d85028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16370 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85624 q = 1) : d85029 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85624, d85029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85624, d85029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d85625 q = 1) : d85030 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85625, d85030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85625, d85030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85626 q = 1) : d85031 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85626, d85031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85626, d85031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85627 q = 1) : d85032 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85627, d85032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85627, d85032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85628 q = 1) : d85033 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85628, d85033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85628, d85033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16372 (p : Pattern) (ha : d8043 p = 1) (hb : d83662 p = 1) : d8096 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8039 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2098 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8040 q = 1) (hb : d83662 q = 1) : d8093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8040, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8041 q = 1) (hb : d83662 q = 1) : d8094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8041, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8042 q = 1) (hb : d83662 q = 1) : d8095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8042, d8095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8042, d8095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8043 q = 1) (hb : d83662 q = 1) : d8096 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8043, d8096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8043, d8096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16373 (p : Pattern) (ha : d8049 p = 1) (hb : d83662 p = 1) : d85043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d83662 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8044 q = 1) (hb : d83662 q = 1) : d85038 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d85038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16372 q ha hb
    | true =>
      simp only [d8044, d85038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8045 q = 1) (hb : d83662 q = 1) : d85039 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d85039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d85039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8046 q = 1) (hb : d83662 q = 1) : d85040 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d85040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8046, d85040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8047 q = 1) (hb : d83662 q = 1) : d85041 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d85041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d85041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8048 q = 1) (hb : d83662 q = 1) : d85042 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d85042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d85042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d8049 q = 1) (hb : d83662 q = 1) : d85043 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8049, d85043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8049, d85043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16374 (p : Pattern) (ha : d8052 p = 1) (hb : d83662 p = 1) : d8117 p = 1 := by
  have h0 (q : Pattern) (ha : d8039 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8040 q = 1) (hb : d83662 q = 1) : d8093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8040, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8041 q = 1) (hb : d83662 q = 1) : d8094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8041, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8042 q = 1) (hb : d83662 q = 1) : d8095 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8042, d8095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8042, d8095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8052 q = 1) (hb : d83662 q = 1) : d8117 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8052, d8117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8052, d8117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16375 (p : Pattern) (ha : d8058 p = 1) (hb : d83662 p = 1) : d85051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d83662 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8044 q = 1) (hb : d83662 q = 1) : d85038 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d85038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16372 q ha hb
    | true =>
      simp only [d8044, d85038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8045 q = 1) (hb : d83662 q = 1) : d85039 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d85039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d85039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8046 q = 1) (hb : d83662 q = 1) : d85040 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d85040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8046, d85040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8047 q = 1) (hb : d83662 q = 1) : d85041 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d85041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d85041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8048 q = 1) (hb : d83662 q = 1) : d85042 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d85042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d85042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2116 q = 1) (hb : d83662 q = 1) : d2116 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8053 q = 1) (hb : d83662 q = 1) : d85046 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8053, d85046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16374 q ha hb
    | true =>
      simp only [d8053, d85046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8054 q = 1) (hb : d83662 q = 1) : d85047 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, d85047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8054, d85047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d8055 q = 1) (hb : d83662 q = 1) : d85048 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, d85048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d8055, d85048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d8056 q = 1) (hb : d83662 q = 1) : d85049 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, d85049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8056, d85049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d8057 q = 1) (hb : d83662 q = 1) : d85050 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, d85050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8057, d85050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d8058 q = 1) (hb : d83662 q = 1) : d85051 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8058, d85051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8058, d85051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16376 (p : Pattern) (ha : d8125 p = 1) (hb : d83662 p = 1) : d85094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2106 q = 1) (hb : d83662 q = 1) : d2106 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8044 q = 1) (hb : d83662 q = 1) : d85038 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8044, d85038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16372 q ha hb
    | true =>
      simp only [d8044, d85038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8045 q = 1) (hb : d83662 q = 1) : d85039 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8045, d85039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8045, d85039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8046 q = 1) (hb : d83662 q = 1) : d85040 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8046, d85040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8046, d85040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8047 q = 1) (hb : d83662 q = 1) : d85041 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8047, d85041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8047, d85041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8048 q = 1) (hb : d83662 q = 1) : d85042 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8048, d85042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8048, d85042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2309 q = 1) (hb : d83662 q = 1) : d2309 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8125 q = 1) (hb : d83662 q = 1) : d85094 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d8125, d85094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d8125, d85094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro16377 (p : Pattern) (ha : d8063 p = 1) (hb : d83662 p = 1) : d85056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8039 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2098 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8040 q = 1) (hb : d83662 q = 1) : d8093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8040, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8041 q = 1) (hb : d83662 q = 1) : d8094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8041, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8062 q = 1) (hb : d83662 q = 1) : d85055 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8062, d85055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8062, d85055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8063 q = 1) (hb : d83662 q = 1) : d85056 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8063, d85056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8063, d85056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16378 (p : Pattern) (ha : d8070 p = 1) (hb : d83662 p = 1) : d85063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8039 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2098 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8040 q = 1) (hb : d83662 q = 1) : d8093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8040, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8068 q = 1) (hb : d83662 q = 1) : d85061 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8068, d85061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8068, d85061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8069 q = 1) (hb : d83662 q = 1) : d85062 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8069, d85062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8069, d85062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8070 q = 1) (hb : d83662 q = 1) : d85063 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8070, d85063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8070, d85063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16379 (p : Pattern) (ha : d8081 p = 1) (hb : d83662 p = 1) : d85070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8077 q = 1) (hb : d77842 q = 1) : d8077 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d8039 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8078 q = 1) (hb : d83662 q = 1) : d85067 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8078, d83662, d85067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8078, d83662, d85067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8079 q = 1) (hb : d83662 q = 1) : d85068 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8079, d85068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8079, d85068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8080 q = 1) (hb : d83662 q = 1) : d85069 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8080, d85069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8080, d85069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8081 q = 1) (hb : d83662 q = 1) : d85070 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8081, d85070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8081, d85070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16380 (p : Pattern) (ha : d83662 p = 1) (hb : d85637 p = 1) : d85076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2129 q = 1) (hb : d83662 q = 1) : d2129 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8064 q = 1) (hb : d83662 q = 1) : d85057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8064, d85057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16377 q ha hb
    | true =>
      simp only [d8064, d85057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8065 q = 1) (hb : d83662 q = 1) : d85058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8065, d85058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8065, d85058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8066 q = 1) (hb : d83662 q = 1) : d85059 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8066, d85059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8066, d85059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8067 q = 1) (hb : d83662 q = 1) : d85060 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8067, d85060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8067, d85060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d83662 q = 1) : d2139 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8071 q = 1) (hb : d83662 q = 1) : d85064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8071, d85064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16378 q ha hb
    | true =>
      simp only [d8071, d85064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8072 q = 1) (hb : d83662 q = 1) : d85065 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8072, d85065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8072, d85065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8073 q = 1) (hb : d83662 q = 1) : d85066 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8073, d85066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8073, d85066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8082 q = 1) (hb : d83662 q = 1) : d85071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8082, d85071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16379 q ha hb
    | true =>
      simp only [d8082, d85071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16372 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85633 q = 1) : d85072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85633, d85072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85633, d85072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8098 q = 1) (hb : d83662 q = 1) : d8098 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d85634 q = 1) : d85073 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85634, d85073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85634, d85073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85635 q = 1) : d85074 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85635, d85074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85635, d85074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d85636 q = 1) : d85075 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85636, d85075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85636, d85075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83662 q = 1) (hb : d85637 q = 1) : d85076 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85637, d85076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85637, d85076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro16381 (p : Pattern) (ha : d8103 p = 1) (hb : d83662 p = 1) : d85077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8039 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2098 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8040 q = 1) (hb : d83662 q = 1) : d8093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8040, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8041 q = 1) (hb : d83662 q = 1) : d8094 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8041, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8041, d8094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8062 q = 1) (hb : d83662 q = 1) : d85055 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8062, d85055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8062, d85055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8103 q = 1) (hb : d83662 q = 1) : d85077 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8103, d85077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8103, d85077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16382 (p : Pattern) (ha : d8108 p = 1) (hb : d83662 p = 1) : d85082 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8039 q = 1) (hb : d77842 q = 1) : d8039 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2098 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d8040 q = 1) (hb : d83662 q = 1) : d8093 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8040, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8040, d83662, d8093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d8068 q = 1) (hb : d83662 q = 1) : d85061 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8068, d85061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8068, d85061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8069 q = 1) (hb : d83662 q = 1) : d85062 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8069, d85062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8069, d85062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d8108 q = 1) (hb : d83662 q = 1) : d85082 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8108, d85082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8108, d85082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16383 (p : Pattern) (ha : d8112 p = 1) (hb : d83662 p = 1) : d85086 p = 1 := by
  have h0 (q : Pattern) (ha : d8077 q = 1) (hb : d77842 q = 1) : d8077 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8039 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8078 q = 1) (hb : d83662 q = 1) : d85067 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8078, d83662, d85067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8078, d83662, d85067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8079 q = 1) (hb : d83662 q = 1) : d85068 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8079, d85068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8079, d85068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8080 q = 1) (hb : d83662 q = 1) : d85069 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8080, d85069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8080, d85069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8112 q = 1) (hb : d83662 q = 1) : d85086 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8112, d85086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8112, d85086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16384 (p : Pattern) (ha : d83662 p = 1) (hb : d85642 p = 1) : d85092 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2129 q = 1) (hb : d83662 q = 1) : d2129 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8064 q = 1) (hb : d83662 q = 1) : d85057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8064, d85057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16377 q ha hb
    | true =>
      simp only [d8064, d85057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8065 q = 1) (hb : d83662 q = 1) : d85058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8065, d85058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8065, d85058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8066 q = 1) (hb : d83662 q = 1) : d85059 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8066, d85059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8066, d85059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8067 q = 1) (hb : d83662 q = 1) : d85060 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8067, d85060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8067, d85060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d83662 q = 1) : d2139 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d8071 q = 1) (hb : d83662 q = 1) : d85064 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8071, d85064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16378 q ha hb
    | true =>
      simp only [d8071, d85064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d8072 q = 1) (hb : d83662 q = 1) : d85065 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8072, d85065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8072, d85065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d8073 q = 1) (hb : d83662 q = 1) : d85066 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8073, d85066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d8073, d85066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d8082 q = 1) (hb : d83662 q = 1) : d85071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8082, d85071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16379 q ha hb
    | true =>
      simp only [d8082, d85071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16372 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85633 q = 1) : d85072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85633, d85072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85633, d85072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d8098 q = 1) (hb : d83662 q = 1) : d8098 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d85634 q = 1) : d85073 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85634, d85073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85634, d85073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85635 q = 1) : d85074 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85635, d85074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85635, d85074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d85636 q = 1) : d85075 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85636, d85075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85636, d85075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2282 q = 1) (hb : d83662 q = 1) : d2282 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d8104 q = 1) (hb : d83662 q = 1) : d85078 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8104, d85078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16381 q ha hb
    | true =>
      simp only [d8104, d85078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d8105 q = 1) (hb : d83662 q = 1) : d85079 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8105, d85079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8105, d85079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d8106 q = 1) (hb : d83662 q = 1) : d85080 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8106, d85080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d8106, d85080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d8107 q = 1) (hb : d83662 q = 1) : d85081 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8107, d85081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8107, d85081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d2288 q = 1) (hb : d83662 q = 1) : d2288 q = 1 := by
    exact ha
  have h22 (q : Pattern) (ha : d8109 q = 1) (hb : d83662 q = 1) : d85083 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8109, d85083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16382 q ha hb
    | true =>
      simp only [d8109, d85083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d8110 q = 1) (hb : d83662 q = 1) : d85084 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8110, d85084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8110, d85084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d8111 q = 1) (hb : d83662 q = 1) : d85085 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8111, d85085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d8111, d85085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d8113 q = 1) (hb : d83662 q = 1) : d85087 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8113, d85087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16383 q ha hb
    | true =>
      simp only [d8113, d85087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16374 q ha hb
  have h26 (q : Pattern) (ha : d83662 q = 1) (hb : d85638 q = 1) : d85088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85638, d85088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d85638, d85088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d8119 q = 1) (hb : d83662 q = 1) : d8119 q = 1 := by
    exact ha
  have h28 (q : Pattern) (ha : d83662 q = 1) (hb : d85639 q = 1) : d85089 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85639, d85089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d85639, d85089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d83662 q = 1) (hb : d85640 q = 1) : d85090 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85640, d85090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
    | true =>
      simp only [d85640, d85090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d83662 q = 1) (hb : d85641 q = 1) : d85091 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85641, d85091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d85641, d85091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d83662 q = 1) (hb : d85642 q = 1) : d85092 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85642, d85092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85642, d85092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro16385 (p : Pattern) (ha : d83662 p = 1) (hb : d85649 p = 1) : d85101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8113 q = 1) (hb : d83662 q = 1) : d85087 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8113, d85087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16383 q ha hb
    | true =>
      simp only [d8113, d85087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16374 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85638 q = 1) : d85088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85638, d85088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85638, d85088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d8119 q = 1) (hb : d83662 q = 1) : d8119 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85639 q = 1) : d85089 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85639, d85089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85639, d85089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85647 q = 1) : d85099 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85647, d85099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85647, d85099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85648 q = 1) : d85100 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85648, d85100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85648, d85100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d85649 q = 1) : d85101 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85649, d85101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85649, d85101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16386 (p : Pattern) (ha : d8149 p = 1) (hb : d83662 p = 1) : d85110 p = 1 := by
  have h0 (q : Pattern) (ha : d8141 q = 1) (hb : d77842 q = 1) : d8141 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d8145 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8146 q = 1) (hb : d83662 q = 1) : d85107 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8146, d83662, d85107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8146, d83662, d85107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8147 q = 1) (hb : d83662 q = 1) : d85108 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8147, d85108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8147, d85108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8148 q = 1) (hb : d83662 q = 1) : d85109 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8148, d85109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8148, d85109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8149 q = 1) (hb : d83662 q = 1) : d85110 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8149, d85110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8149, d85110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16387 (p : Pattern) (ha : d8153 p = 1) (hb : d83662 p = 1) : d8168 p = 1 := by
  have h0 (q : Pattern) (ha : d8145 q = 1) (hb : d77842 q = 1) : d8145 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2387 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8150 q = 1) (hb : d83662 q = 1) : d8165 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d8150, d83662, d8165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8150, d83662, d8165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d8151 q = 1) (hb : d83662 q = 1) : d8166 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d8151, d8166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8151, d8166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d8152 q = 1) (hb : d83662 q = 1) : d8167 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d8152, d8167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d8152, d8167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d8153 q = 1) (hb : d83662 q = 1) : d8168 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d8153, d8168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d8153, d8168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16388 (p : Pattern) (ha : d83662 p = 1) (hb : d85659 p = 1) : d85116 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8154 q = 1) (hb : d83662 q = 1) : d85111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8154, d85111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16386 q ha hb
    | true =>
      simp only [d8154, d85111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16387 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85655 q = 1) : d85112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85655, d85112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85655, d85112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d8170 q = 1) (hb : d83662 q = 1) : d8170 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85656 q = 1) : d85113 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85656, d85113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85656, d85113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85657 q = 1) : d85114 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85657, d85114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85657, d85114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85658 q = 1) : d85115 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85658, d85115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85658, d85115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d85659 q = 1) : d85116 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85659, d85116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85659, d85116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16389 (p : Pattern) (ha : d83662 p = 1) (hb : d85665 p = 1) : d85122 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8050 q = 1) (hb : d83662 q = 1) : d85044 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8050, d85044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8050, d85044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16373 q ha hb
  have h2 (q : Pattern) (ha : d8051 q = 1) (hb : d83662 q = 1) : d85045 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8051, d85045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8051, d85045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d8059 q = 1) (hb : d83662 q = 1) : d85052 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8059, d85052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16373 q ha hb
    | true =>
      simp only [d8059, d85052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16375 q ha hb
  have h4 (q : Pattern) (ha : d8060 q = 1) (hb : d83662 q = 1) : d85053 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8060, d85053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8060, d85053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8061 q = 1) (hb : d83662 q = 1) : d85054 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d8061, d85054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d8061, d85054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85643 q = 1) : d85093 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85643, d85093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16380 q ha hb
    | true =>
      simp only [d85643, d85093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16384 q ha hb
  have h7 (q : Pattern) (ha : d2316 q = 1) (hb : d83662 q = 1) : d2316 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d8126 q = 1) (hb : d83662 q = 1) : d85095 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8126, d85095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16376 q ha hb
    | true =>
      simp only [d8126, d85095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83662 q = 1) (hb : d85644 q = 1) : d85096 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85644, d85096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85644, d85096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d83662 q = 1) (hb : d85645 q = 1) : d85097 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85645, d85097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85645, d85097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85646 q = 1) : d85098 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85646, d85098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85646, d85098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d83662 q = 1) (hb : d85650 q = 1) : d85102 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85650, d85102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85650, d85102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16385 q ha hb
  have h13 (q : Pattern) (ha : d2326 q = 1) (hb : d83662 q = 1) : d2326 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85651 q = 1) : d85103 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85651, d85103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85651, d85103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d85652 q = 1) : d85104 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85652, d85104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85652, d85104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d83662 q = 1) (hb : d85653 q = 1) : d85105 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85653, d85105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85653, d85105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h17 (q : Pattern) (ha : d83662 q = 1) (hb : d85654 q = 1) : d85106 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85654, d85106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85654, d85106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d83662 q = 1) (hb : d85660 q = 1) : d85117 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85660, d85117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85660, d85117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16388 q ha hb
  have h19 (q : Pattern) (ha : d2459 q = 1) (hb : d83662 q = 1) : d2459 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d83662 q = 1) (hb : d85661 q = 1) : d85118 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85661, d85118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85661, d85118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d83662 q = 1) (hb : d85662 q = 1) : d85119 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85662, d85119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85662, d85119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d83662 q = 1) (hb : d85663 q = 1) : d85120 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85663, d85120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85663, d85120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d83662 q = 1) (hb : d85664 q = 1) : d85121 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85664, d85121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d85664, d85121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h24 (q : Pattern) (ha : d83662 q = 1) (hb : d85665 q = 1) : d85122 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85665, d85122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85665, d85122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  exact h24 p ha hb
theorem andIntro16390 (p : Pattern) (ha : d83662 p = 1) (hb : d85671 p = 1) : d85128 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d85666 q = 1) : d85123 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85666, d85123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85666, d85123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16389 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85667 q = 1) : d85124 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85667, d85124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85667, d85124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d85668 q = 1) : d85125 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85668, d85125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85668, d85125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85669 q = 1) : d85126 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85669, d85126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85669, d85126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85670 q = 1) : d85127 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85670, d85127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85670, d85127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85671 q = 1) : d85128 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85671, d85128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85671, d85128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16391 (p : Pattern) (ha : d83662 p = 1) (hb : d85677 p = 1) : d85134 p = 1 := by
  have h0 (q : Pattern) (ha : d83662 q = 1) (hb : d85506 q = 1) : d84755 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85506, d84755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16295 q ha hb
    | true =>
      simp only [d85506, d84755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16314 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85546 q = 1) : d84847 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85546, d84847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85546, d84847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16333 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d85547 q = 1) : d84848 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85547, d84848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d85547, d84848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85587 q = 1) : d84940 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85587, d84940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85587, d84940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16352 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85588 q = 1) : d84941 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85588, d84941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85588, d84941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85589 q = 1) : d84942 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85589, d84942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85589, d84942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d85629 q = 1) : d85034 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85629, d85034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85629, d85034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16371 q ha hb
  have h8 (q : Pattern) (ha : d83662 q = 1) (hb : d85630 q = 1) : d85035 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85630, d85035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85630, d85035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83662 q = 1) (hb : d85631 q = 1) : d85036 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85631, d85036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85631, d85036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83662 q = 1) (hb : d85632 q = 1) : d85037 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d85632, d85037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85632, d85037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d85672 q = 1) : d85129 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d85672, d85129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85672, d85129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16390 q ha hb
  have h12 (q : Pattern) (ha : d83662 q = 1) (hb : d85673 q = 1) : d85130 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d85673, d85130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85673, d85130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d85674 q = 1) : d85131 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d85674, d85131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85674, d85131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d85675 q = 1) : d85132 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d85675, d85132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d85675, d85132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d85676 q = 1) : d85133 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d85676, d85133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85676, d85133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83662 q = 1) (hb : d85677 q = 1) : d85134 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d85677, d85134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85677, d85134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro16392 (p : Pattern) (ha : d83662 p = 1) (hb : d85683 p = 1) : d85140 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d85678 q = 1) : d85135 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d85678, d85135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16391 q ha hb
    | true =>
      simp only [d85678, d85135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85679 q = 1) : d85136 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d85679, d85136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85679, d85136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d85680 q = 1) : d85137 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d85680, d85137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85680, d85137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85681 q = 1) : d85138 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d85681, d85138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85681, d85138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85682 q = 1) : d85139 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d85682, d85139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85682, d85139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85683 q = 1) : d85140 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d85683, d85140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85683, d85140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16393 (p : Pattern) (ha : d83662 p = 1) (hb : d85689 p = 1) : d85146 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d85684 q = 1) : d85141 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d85684, d85141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16392 q ha hb
    | true =>
      simp only [d85684, d85141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85685 q = 1) : d85142 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d85685, d85142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85685, d85142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d85686 q = 1) : d85143 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d85686, d85143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85686, d85143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85687 q = 1) : d85144 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d85687, d85144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85687, d85144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85688 q = 1) : d85145 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d85688, d85145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85688, d85145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85689 q = 1) : d85146 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d85689, d85146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85689, d85146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16394 (p : Pattern) (ha : d83662 p = 1) (hb : d85695 p = 1) : d85152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d85690 q = 1) : d85147 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d85690, d85147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16393 q ha hb
    | true =>
      simp only [d85690, d85147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85691 q = 1) : d85148 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d85691, d85148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85691, d85148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d85692 q = 1) : d85149 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d85692, d85149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85692, d85149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85693 q = 1) : d85150 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d85693, d85150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85693, d85150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85694 q = 1) : d85151 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d85694, d85151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85694, d85151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85695 q = 1) : d85152 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d85695, d85152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85695, d85152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16395 (p : Pattern) (ha : d83662 p = 1) (hb : d85701 p = 1) : d85158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d85696 q = 1) : d85153 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d85696, d85153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16394 q ha hb
    | true =>
      simp only [d85696, d85153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85697 q = 1) : d85154 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d85697, d85154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85697, d85154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d85698 q = 1) : d85155 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d85698, d85155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85698, d85155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85699 q = 1) : d85156 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d85699, d85156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85699, d85156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85700 q = 1) : d85157 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d85700, d85157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85700, d85157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85701 q = 1) : d85158 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d85701, d85158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85701, d85158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16396 (p : Pattern) (ha : d83662 p = 1) (hb : d85707 p = 1) : d85164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d85702 q = 1) : d85159 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d85702, d85159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16395 q ha hb
    | true =>
      simp only [d85702, d85159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85703 q = 1) : d85160 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d85703, d85160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85703, d85160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d85704 q = 1) : d85161 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d85704, d85161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85704, d85161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85705 q = 1) : d85162 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d85705, d85162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85705, d85162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85706 q = 1) : d85163 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d85706, d85163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85706, d85163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85707 q = 1) : d85164 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d85707, d85164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85707, d85164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16397 (p : Pattern) (ha : d83662 p = 1) (hb : d85713 p = 1) : d85170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d85708 q = 1) : d85165 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d85708, d85165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16396 q ha hb
    | true =>
      simp only [d85708, d85165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85709 q = 1) : d85166 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d85709, d85166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85709, d85166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d85710 q = 1) : d85167 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d85710, d85167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85710, d85167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85711 q = 1) : d85168 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d85711, d85168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85711, d85168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85712 q = 1) : d85169 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d85712, d85169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85712, d85169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85713 q = 1) : d85170 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d85713, d85170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85713, d85170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16398 (p : Pattern) (ha : d83662 p = 1) (hb : d85719 p = 1) : d85176 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d85714 q = 1) : d85171 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d85714, d85171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16397 q ha hb
    | true =>
      simp only [d85714, d85171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d85715 q = 1) : d85172 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d85715, d85172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d85715, d85172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d85716 q = 1) : d85173 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d85716, d85173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d85716, d85173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d85717 q = 1) : d85174 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d85717, d85174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85717, d85174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d85718 q = 1) : d85175 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d85718, d85175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d85718, d85175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d85719 q = 1) : d85176 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d85719, d85176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85719, d85176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16399 (p : Pattern) (ha : d83662 p = 1) (hb : d99199 p = 1) : d85179 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d83662 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7255 q = 1) (hb : d83662 q = 1) : d84549 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16274 q ha hb
    | true =>
      simp only [d7255, d84549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7305 q = 1) (hb : d83662 q = 1) : d84591 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7305, d84591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7305, d84591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7306 q = 1) (hb : d83662 q = 1) : d84592 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7306, d84592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7306, d84592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7307 q = 1) (hb : d83662 q = 1) : d84593 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7307, d84593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7307, d84593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7308 q = 1) (hb : d83662 q = 1) : d84594 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7308, d84594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7308, d84594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d99199 q = 1) : d85179 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99199, d85179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99199, d85179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro16400 (p : Pattern) (ha : d83662 p = 1) (hb : d99209 p = 1) : d85189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d83662 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7281 q = 1) (hb : d83662 q = 1) : d84567 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7281, d84567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16277 q ha hb
    | true =>
      simp only [d7281, d84567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99205 q = 1) : d85185 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99205, d85185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99205, d85185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99206 q = 1) : d85186 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99206, d85186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99206, d85186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99207 q = 1) : d85187 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99207, d85187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99207, d85187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99208 q = 1) : d85188 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99208, d85188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99208, d85188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d99209 q = 1) : d85189 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99209, d85189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99209, d85189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16401 (p : Pattern) (ha : d83662 p = 1) (hb : d99215 p = 1) : d85195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7310 q = 1) (hb : d83662 q = 1) : d84596 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7310, d84596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16280 q ha hb
    | true =>
      simp only [d7310, d84596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16281 q ha hb
  have h2 (q : Pattern) (ha : d7311 q = 1) (hb : d83662 q = 1) : d84597 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7311, d84597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7311, d84597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99197 q = 1) : d85177 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99197, d85177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d99197, d85177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99198 q = 1) : d85178 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99198, d85178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99198, d85178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99200 q = 1) : d85180 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99200, d85180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99200, d85180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16399 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99201 q = 1) : d85181 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99201, d85181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99201, d85181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d99202 q = 1) : d85182 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99202, d85182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99202, d85182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83662 q = 1) (hb : d99203 q = 1) : d85183 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99203, d85183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99203, d85183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d83662 q = 1) (hb : d99204 q = 1) : d85184 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99204, d85184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99204, d85184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83662 q = 1) (hb : d99210 q = 1) : d85190 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99210, d85190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99210, d85190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16400 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d99211 q = 1) : d85191 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99211, d85191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99211, d85191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d83662 q = 1) (hb : d99212 q = 1) : d85192 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99212, d85192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99212, d85192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d99213 q = 1) : d85193 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99213, d85193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99213, d85193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d99214 q = 1) : d85194 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99214, d85194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99214, d85194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d99215 q = 1) : d85195 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99215, d85195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99215, d85195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16402 (p : Pattern) (ha : d83662 p = 1) (hb : d99221 p = 1) : d85201 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d83662 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d99216 q = 1) : d85196 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99216, d85196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99216, d85196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16401 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99217 q = 1) : d85197 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99217, d85197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99217, d85197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99218 q = 1) : d85198 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99218, d85198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99218, d85198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99219 q = 1) : d85199 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99219, d85199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99219, d85199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99220 q = 1) : d85200 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99220, d85200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99220, d85200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d99221 q = 1) : d85201 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99221, d85201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99221, d85201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16403 (p : Pattern) (ha : d83662 p = 1) (hb : d99224 p = 1) : d85204 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d501 q = 1) (hb : d83662 q = 1) : d501 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7443 q = 1) (hb : d83662 q = 1) : d84672 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7443, d84672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16298 q ha hb
    | true =>
      simp only [d7443, d84672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7444 q = 1) (hb : d83662 q = 1) : d84673 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7444, d84673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7444, d84673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7445 q = 1) (hb : d83662 q = 1) : d84674 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7445, d84674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7445, d84674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7446 q = 1) (hb : d83662 q = 1) : d84675 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7446, d84675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7446, d84675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7447 q = 1) (hb : d83662 q = 1) : d84676 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7447, d84676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7447, d84676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d99224 q = 1) : d85204 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99224, d85204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99224, d85204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro16404 (p : Pattern) (ha : d83662 p = 1) (hb : d99235 p = 1) : d85215 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d730 q = 1) (hb : d83662 q = 1) : d730 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d99230 q = 1) : d85210 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99230, d85210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16311 q hb ha
    | true =>
      simp only [d99230, d85210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99231 q = 1) : d85211 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99231, d85211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99231, d85211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99232 q = 1) : d85212 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99232, d85212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99232, d85212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99233 q = 1) : d85213 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99233, d85213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99233, d85213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99234 q = 1) : d85214 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99234, d85214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99234, d85214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d99235 q = 1) : d85215 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99235, d85215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99235, d85215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16405 (p : Pattern) (ha : d83662 p = 1) (hb : d99241 p = 1) : d85221 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7449 q = 1) (hb : d83662 q = 1) : d84678 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7449, d84678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16297 q ha hb
    | true =>
      simp only [d7449, d84678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16299 q ha hb
  have h2 (q : Pattern) (ha : d7450 q = 1) (hb : d83662 q = 1) : d84679 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7450, d84679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7450, d84679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99222 q = 1) : d85202 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99222, d85202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d99222, d85202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99223 q = 1) : d85203 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99223, d85203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99223, d85203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99225 q = 1) : d85205 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99225, d85205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99225, d85205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16403 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99226 q = 1) : d85206 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99226, d85206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99226, d85206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d99227 q = 1) : d85207 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99227, d85207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99227, d85207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83662 q = 1) (hb : d99228 q = 1) : d85208 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99228, d85208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99228, d85208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d83662 q = 1) (hb : d99229 q = 1) : d85209 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99229, d85209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99229, d85209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83662 q = 1) (hb : d99236 q = 1) : d85216 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99236, d85216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99236, d85216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16404 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d99237 q = 1) : d85217 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99237, d85217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99237, d85217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d83662 q = 1) (hb : d99238 q = 1) : d85218 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99238, d85218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99238, d85218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d99239 q = 1) : d85219 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99239, d85219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99239, d85219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d99240 q = 1) : d85220 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99240, d85220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99240, d85220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d99241 q = 1) : d85221 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99241, d85221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99241, d85221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16406 (p : Pattern) (ha : d83662 p = 1) (hb : d99247 p = 1) : d85227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d99242 q = 1) : d85222 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99242, d85222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99242, d85222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16405 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d99243 q = 1) : d85223 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99243, d85223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99243, d85223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99244 q = 1) : d85224 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99244, d85224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99244, d85224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99245 q = 1) : d85225 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99245, d85225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99245, d85225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99246 q = 1) : d85226 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99246, d85226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99246, d85226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99247 q = 1) : d85227 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99247, d85227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99247, d85227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16407 (p : Pattern) (ha : d83662 p = 1) (hb : d99251 p = 1) : d85231 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d793 q = 1) (hb : d83662 q = 1) : d793 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7591 q = 1) (hb : d83662 q = 1) : d84764 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7591, d84764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16317 q ha hb
    | true =>
      simp only [d7591, d84764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7592 q = 1) (hb : d83662 q = 1) : d84765 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, d84765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7592, d84765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7593 q = 1) (hb : d83662 q = 1) : d84766 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, d84766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7593, d84766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7594 q = 1) (hb : d83662 q = 1) : d84767 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, d84767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7594, d84767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7595 q = 1) (hb : d83662 q = 1) : d84768 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, d84768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7595, d84768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d99251 q = 1) : d85231 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99251, d85231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99251, d85231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro16408 (p : Pattern) (ha : d83662 p = 1) (hb : d99262 p = 1) : d85242 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1063 q = 1) (hb : d83662 q = 1) : d1063 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d99257 q = 1) : d85237 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99257, d85237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16330 q hb ha
    | true =>
      simp only [d99257, d85237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99258 q = 1) : d85238 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99258, d85238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99258, d85238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99259 q = 1) : d85239 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99259, d85239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99259, d85239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99260 q = 1) : d85240 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99260, d85240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99260, d85240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99261 q = 1) : d85241 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99261, d85241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99261, d85241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d99262 q = 1) : d85242 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99262, d85242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99262, d85242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16409 (p : Pattern) (ha : d83662 p = 1) (hb : d99268 p = 1) : d85248 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7597 q = 1) (hb : d83662 q = 1) : d84770 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7597, d84770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16316 q ha hb
    | true =>
      simp only [d7597, d84770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16318 q ha hb
  have h2 (q : Pattern) (ha : d7598 q = 1) (hb : d83662 q = 1) : d84771 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7598, d84771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7598, d84771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99249 q = 1) : d85229 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99249, d85229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d99249, d85229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99250 q = 1) : d85230 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99250, d85230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99250, d85230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99252 q = 1) : d85232 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99252, d85232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99252, d85232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16407 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99253 q = 1) : d85233 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99253, d85233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99253, d85233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d99254 q = 1) : d85234 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99254, d85234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99254, d85234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83662 q = 1) (hb : d99255 q = 1) : d85235 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99255, d85235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99255, d85235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d83662 q = 1) (hb : d99256 q = 1) : d85236 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99256, d85236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99256, d85236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83662 q = 1) (hb : d99263 q = 1) : d85243 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99263, d85243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99263, d85243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16408 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d99264 q = 1) : d85244 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99264, d85244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99264, d85244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d83662 q = 1) (hb : d99265 q = 1) : d85245 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99265, d85245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99265, d85245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d99266 q = 1) : d85246 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99266, d85246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99266, d85246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d99267 q = 1) : d85247 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99267, d85247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99267, d85247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d99268 q = 1) : d85248 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99268, d85248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99268, d85248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16410 (p : Pattern) (ha : d83662 p = 1) (hb : d99274 p = 1) : d85254 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d99269 q = 1) : d85249 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99269, d85249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99269, d85249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16409 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d99270 q = 1) : d85250 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99270, d85250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99270, d85250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99271 q = 1) : d85251 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99271, d85251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99271, d85251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99272 q = 1) : d85252 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99272, d85252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99272, d85252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99273 q = 1) : d85253 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99273, d85253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99273, d85253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99274 q = 1) : d85254 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99274, d85254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99274, d85254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16411 (p : Pattern) (ha : d83662 p = 1) (hb : d99279 p = 1) : d85259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1172 q = 1) (hb : d83662 q = 1) : d1172 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7744 q = 1) (hb : d83662 q = 1) : d84857 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7744, d84857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16336 q ha hb
    | true =>
      simp only [d7744, d84857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7745 q = 1) (hb : d83662 q = 1) : d84858 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7745, d84858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7745, d84858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7746 q = 1) (hb : d83662 q = 1) : d84859 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7746, d84859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7746, d84859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7747 q = 1) (hb : d83662 q = 1) : d84860 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7747, d84860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7747, d84860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7748 q = 1) (hb : d83662 q = 1) : d84861 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7748, d84861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7748, d84861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d99279 q = 1) : d85259 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99279, d85259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99279, d85259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro16412 (p : Pattern) (ha : d83662 p = 1) (hb : d99290 p = 1) : d85270 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1497 q = 1) (hb : d83662 q = 1) : d1497 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d99285 q = 1) : d85265 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99285, d85265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16349 q hb ha
    | true =>
      simp only [d99285, d85265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99286 q = 1) : d85266 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99286, d85266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99286, d85266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99287 q = 1) : d85267 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99287, d85267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99287, d85267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99288 q = 1) : d85268 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99288, d85268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99288, d85268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99289 q = 1) : d85269 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99289, d85269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99289, d85269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d99290 q = 1) : d85270 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99290, d85270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99290, d85270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16413 (p : Pattern) (ha : d83662 p = 1) (hb : d99296 p = 1) : d85276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7750 q = 1) (hb : d83662 q = 1) : d84863 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7750, d84863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16335 q ha hb
    | true =>
      simp only [d7750, d84863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16337 q ha hb
  have h2 (q : Pattern) (ha : d7751 q = 1) (hb : d83662 q = 1) : d84864 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7751, d84864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7751, d84864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99277 q = 1) : d85257 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99277, d85257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d99277, d85257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99278 q = 1) : d85258 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99278, d85258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99278, d85258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99280 q = 1) : d85260 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99280, d85260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99280, d85260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16411 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99281 q = 1) : d85261 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99281, d85261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99281, d85261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d99282 q = 1) : d85262 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99282, d85262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99282, d85262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83662 q = 1) (hb : d99283 q = 1) : d85263 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99283, d85263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99283, d85263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d83662 q = 1) (hb : d99284 q = 1) : d85264 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99284, d85264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99284, d85264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83662 q = 1) (hb : d99291 q = 1) : d85271 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99291, d85271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99291, d85271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16412 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d99292 q = 1) : d85272 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99292, d85272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99292, d85272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d83662 q = 1) (hb : d99293 q = 1) : d85273 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99293, d85273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99293, d85273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d99294 q = 1) : d85274 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99294, d85274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99294, d85274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d99295 q = 1) : d85275 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99295, d85275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99295, d85275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d99296 q = 1) : d85276 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99296, d85276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99296, d85276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16414 (p : Pattern) (ha : d83662 p = 1) (hb : d99302 p = 1) : d85282 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d99297 q = 1) : d85277 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99297, d85277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99297, d85277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16413 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d99298 q = 1) : d85278 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99298, d85278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99298, d85278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99299 q = 1) : d85279 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99299, d85279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99299, d85279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99300 q = 1) : d85280 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99300, d85280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99300, d85280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99301 q = 1) : d85281 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99301, d85281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99301, d85281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99302 q = 1) : d85282 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99302, d85282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99302, d85282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16415 (p : Pattern) (ha : d83662 p = 1) (hb : d99308 p = 1) : d85288 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1633 q = 1) (hb : d83662 q = 1) : d1633 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7898 q = 1) (hb : d83662 q = 1) : d84951 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7898, d84951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16355 q ha hb
    | true =>
      simp only [d7898, d84951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d7899 q = 1) (hb : d83662 q = 1) : d84952 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7899, d84952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7899, d84952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7900 q = 1) (hb : d83662 q = 1) : d84953 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7900, d84953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7900, d84953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7901 q = 1) (hb : d83662 q = 1) : d84954 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7901, d84954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7901, d84954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7902 q = 1) (hb : d83662 q = 1) : d84955 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7902, d84955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7902, d84955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d99308 q = 1) : d85288 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99308, d85288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99308, d85288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro16416 (p : Pattern) (ha : d83662 p = 1) (hb : d99319 p = 1) : d85299 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1974 q = 1) (hb : d83662 q = 1) : d1974 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d99314 q = 1) : d85294 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99314, d85294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16368 q hb ha
    | true =>
      simp only [d99314, d85294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99315 q = 1) : d85295 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99315, d85295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99315, d85295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99316 q = 1) : d85296 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99316, d85296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99316, d85296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99317 q = 1) : d85297 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99317, d85297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99317, d85297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99318 q = 1) : d85298 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99318, d85298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99318, d85298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d99319 q = 1) : d85299 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99319, d85299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99319, d85299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16417 (p : Pattern) (ha : d83662 p = 1) (hb : d99325 p = 1) : d85305 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7904 q = 1) (hb : d83662 q = 1) : d84957 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7904, d84957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16354 q ha hb
    | true =>
      simp only [d7904, d84957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16356 q ha hb
  have h2 (q : Pattern) (ha : d7905 q = 1) (hb : d83662 q = 1) : d84958 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7905, d84958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7905, d84958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99306 q = 1) : d85286 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99306, d85286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d99306, d85286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99307 q = 1) : d85287 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99307, d85287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99307, d85287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99309 q = 1) : d85289 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99309, d85289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99309, d85289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16415 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99310 q = 1) : d85290 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99310, d85290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99310, d85290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d99311 q = 1) : d85291 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99311, d85291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99311, d85291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83662 q = 1) (hb : d99312 q = 1) : d85292 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99312, d85292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99312, d85292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d83662 q = 1) (hb : d99313 q = 1) : d85293 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99313, d85293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99313, d85293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83662 q = 1) (hb : d99320 q = 1) : d85300 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99320, d85300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99320, d85300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16416 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d99321 q = 1) : d85301 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99321, d85301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99321, d85301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d83662 q = 1) (hb : d99322 q = 1) : d85302 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99322, d85302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99322, d85302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d99323 q = 1) : d85303 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99323, d85303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99323, d85303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d99324 q = 1) : d85304 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99324, d85304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99324, d85304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d99325 q = 1) : d85305 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99325, d85305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99325, d85305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16418 (p : Pattern) (ha : d83662 p = 1) (hb : d99331 p = 1) : d85311 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d99326 q = 1) : d85306 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99326, d85306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99326, d85306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16417 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d99327 q = 1) : d85307 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99327, d85307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99327, d85307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99328 q = 1) : d85308 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99328, d85308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99328, d85308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99329 q = 1) : d85309 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99329, d85309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99329, d85309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99330 q = 1) : d85310 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99330, d85310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99330, d85310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99331 q = 1) : d85311 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99331, d85311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99331, d85311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16419 (p : Pattern) (ha : d83662 p = 1) (hb : d99338 p = 1) : d85318 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2116 q = 1) (hb : d83662 q = 1) : d2116 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d8053 q = 1) (hb : d83662 q = 1) : d85046 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d8053, d85046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16374 q ha hb
    | true =>
      simp only [d8053, d85046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d8054 q = 1) (hb : d83662 q = 1) : d85047 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d8054, d85047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8054, d85047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d8055 q = 1) (hb : d83662 q = 1) : d85048 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d8055, d85048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d8055, d85048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d8056 q = 1) (hb : d83662 q = 1) : d85049 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d8056, d85049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8056, d85049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d8057 q = 1) (hb : d83662 q = 1) : d85050 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d8057, d85050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d8057, d85050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d99338 q = 1) : d85318 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99338, d85318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99338, d85318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  exact h7 p ha hb
theorem andIntro16420 (p : Pattern) (ha : d83662 p = 1) (hb : d99349 p = 1) : d85329 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2452 q = 1) (hb : d83662 q = 1) : d2452 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d99344 q = 1) : d85324 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99344, d85324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16387 q hb ha
    | true =>
      simp only [d99344, d85324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99345 q = 1) : d85325 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99345, d85325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99345, d85325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99346 q = 1) : d85326 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99346, d85326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99346, d85326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99347 q = 1) : d85327 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99347, d85327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99347, d85327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99348 q = 1) : d85328 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99348, d85328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99348, d85328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d99349 q = 1) : d85329 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99349, d85329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99349, d85329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16421 (p : Pattern) (ha : d83662 p = 1) (hb : d99355 p = 1) : d85335 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d8059 q = 1) (hb : d83662 q = 1) : d85052 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d8059, d85052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16373 q ha hb
    | true =>
      simp only [d8059, d85052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16375 q ha hb
  have h2 (q : Pattern) (ha : d8060 q = 1) (hb : d83662 q = 1) : d85053 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d8060, d85053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d8060, d85053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99336 q = 1) : d85316 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99336, d85316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d99336, d85316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99337 q = 1) : d85317 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99337, d85317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99337, d85317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99339 q = 1) : d85319 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99339, d85319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99339, d85319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16419 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99340 q = 1) : d85320 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99340, d85320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99340, d85320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d99341 q = 1) : d85321 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99341, d85321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99341, d85321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d83662 q = 1) (hb : d99342 q = 1) : d85322 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99342, d85322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d99342, d85322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d83662 q = 1) (hb : d99343 q = 1) : d85323 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99343, d85323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99343, d85323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83662 q = 1) (hb : d99350 q = 1) : d85330 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99350, d85330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99350, d85330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16420 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d99351 q = 1) : d85331 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99351, d85331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99351, d85331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d83662 q = 1) (hb : d99352 q = 1) : d85332 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99352, d85332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d99352, d85332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d99353 q = 1) : d85333 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99353, d85333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d99353, d85333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d99354 q = 1) : d85334 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99354, d85334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d99354, d85334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d99355 q = 1) : d85335 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99355, d85335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d99355, d85335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16422 (p : Pattern) (ha : d83662 p = 1) (hb : d99361 p = 1) : d85341 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d99356 q = 1) : d85336 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99356, d85336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99356, d85336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16421 q ha hb
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d99357 q = 1) : d85337 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99357, d85337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99357, d85337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99358 q = 1) : d85338 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99358, d85338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99358, d85338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99359 q = 1) : d85339 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99359, d85339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99359, d85339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99360 q = 1) : d85340 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99360, d85340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99360, d85340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99361 q = 1) : d85341 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99361, d85341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d99361, d85341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16423 (p : Pattern) (ha : d83662 p = 1) (hb : d99367 p = 1) : d85347 p = 1 := by
  have h0 (q : Pattern) (ha : d83662 q = 1) (hb : d99248 q = 1) : d85228 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d99248, d85228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16402 q ha hb
    | true =>
      simp only [d99248, d85228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16406 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d99275 q = 1) : d85255 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d99275, d85255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99275, d85255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16410 q ha hb
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99276 q = 1) : d85256 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d99276, d85256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99276, d85256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99303 q = 1) : d85283 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d99303, d85283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99303, d85283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16414 q ha hb
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99304 q = 1) : d85284 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d99304, d85284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99304, d85284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99305 q = 1) : d85285 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d99305, d85285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99305, d85285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d83662 q = 1) (hb : d99332 q = 1) : d85312 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d99332, d85312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99332, d85312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16418 q ha hb
  have h8 (q : Pattern) (ha : d83662 q = 1) (hb : d99333 q = 1) : d85313 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d99333, d85313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99333, d85313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d83662 q = 1) (hb : d99334 q = 1) : d85314 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d99334, d85314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99334, d85314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d83662 q = 1) (hb : d99335 q = 1) : d85315 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d99335, d85315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d99335, d85315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d83662 q = 1) (hb : d99362 q = 1) : d85342 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d99362, d85342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99362, d85342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16422 q ha hb
  have h12 (q : Pattern) (ha : d83662 q = 1) (hb : d99363 q = 1) : d85343 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d99363, d85343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99363, d85343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d83662 q = 1) (hb : d99364 q = 1) : d85344 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d99364, d85344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99364, d85344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d83662 q = 1) (hb : d99365 q = 1) : d85345 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d99365, d85345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d99365, d85345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d83662 q = 1) (hb : d99366 q = 1) : d85346 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d99366, d85346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d99366, d85346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d83662 q = 1) (hb : d99367 q = 1) : d85347 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d99367, d85347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d99367, d85347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro16424 (p : Pattern) (ha : d83662 p = 1) (hb : d99373 p = 1) : d85353 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d99368 q = 1) : d85348 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d99368, d85348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16423 q ha hb
    | true =>
      simp only [d99368, d85348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d99369 q = 1) : d85349 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d99369, d85349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99369, d85349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99370 q = 1) : d85350 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d99370, d85350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99370, d85350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99371 q = 1) : d85351 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d99371, d85351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99371, d85351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99372 q = 1) : d85352 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d99372, d85352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99372, d85352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99373 q = 1) : d85353 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d99373, d85353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99373, d85353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16425 (p : Pattern) (ha : d83662 p = 1) (hb : d99379 p = 1) : d85359 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d99374 q = 1) : d85354 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d99374, d85354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16424 q ha hb
    | true =>
      simp only [d99374, d85354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d99375 q = 1) : d85355 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d99375, d85355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99375, d85355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99376 q = 1) : d85356 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d99376, d85356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99376, d85356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99377 q = 1) : d85357 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d99377, d85357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99377, d85357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99378 q = 1) : d85358 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d99378, d85358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99378, d85358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99379 q = 1) : d85359 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d99379, d85359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99379, d85359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16426 (p : Pattern) (ha : d83662 p = 1) (hb : d99385 p = 1) : d85365 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d99380 q = 1) : d85360 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d99380, d85360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16425 q ha hb
    | true =>
      simp only [d99380, d85360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d99381 q = 1) : d85361 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d99381, d85361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99381, d85361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99382 q = 1) : d85362 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d99382, d85362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99382, d85362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99383 q = 1) : d85363 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d99383, d85363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99383, d85363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99384 q = 1) : d85364 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d99384, d85364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99384, d85364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99385 q = 1) : d85365 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d99385, d85365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99385, d85365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16427 (p : Pattern) (ha : d83662 p = 1) (hb : d99391 p = 1) : d85371 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d99386 q = 1) : d85366 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d99386, d85366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16426 q ha hb
    | true =>
      simp only [d99386, d85366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d99387 q = 1) : d85367 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d99387, d85367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99387, d85367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99388 q = 1) : d85368 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d99388, d85368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99388, d85368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99389 q = 1) : d85369 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d99389, d85369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99389, d85369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99390 q = 1) : d85370 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d99390, d85370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99390, d85370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99391 q = 1) : d85371 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d99391, d85371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99391, d85371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16428 (p : Pattern) (ha : d83662 p = 1) (hb : d99397 p = 1) : d85377 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d99392 q = 1) : d85372 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d99392, d85372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16427 q ha hb
    | true =>
      simp only [d99392, d85372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d99393 q = 1) : d85373 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d99393, d85373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99393, d85373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99394 q = 1) : d85374 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d99394, d85374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99394, d85374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99395 q = 1) : d85375 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d99395, d85375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99395, d85375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99396 q = 1) : d85376 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d99396, d85376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99396, d85376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99397 q = 1) : d85377 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d99397, d85377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99397, d85377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16429 (p : Pattern) (ha : d83662 p = 1) (hb : d99403 p = 1) : d85383 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d99398 q = 1) : d85378 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d99398, d85378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16428 q ha hb
    | true =>
      simp only [d99398, d85378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d99399 q = 1) : d85379 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d99399, d85379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99399, d85379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99400 q = 1) : d85380 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d99400, d85380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99400, d85380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99401 q = 1) : d85381 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d99401, d85381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99401, d85381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99402 q = 1) : d85382 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d99402, d85382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99402, d85382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99403 q = 1) : d85383 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d99403, d85383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99403, d85383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16430 (p : Pattern) (ha : d83662 p = 1) (hb : d99409 p = 1) : d85389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d83662 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83662 q = 1) (hb : d99404 q = 1) : d85384 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d99404, d85384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16429 q ha hb
    | true =>
      simp only [d99404, d85384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d83662 q = 1) (hb : d99405 q = 1) : d85385 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d99405, d85385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d99405, d85385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d83662 q = 1) (hb : d99406 q = 1) : d85386 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d99406, d85386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d99406, d85386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d83662 q = 1) (hb : d99407 q = 1) : d85387 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d99407, d85387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d99407, d85387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d83662 q = 1) (hb : d99408 q = 1) : d85388 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d99408, d85388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d99408, d85388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d83662 q = 1) (hb : d99409 q = 1) : d85389 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d99409, d85389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d99409, d85389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro16431 (p : Pattern) (ha : d7247 p = 1) (hb : d77844 p = 1) : d79651 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7243 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d77842 q = 1) : d38 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7244 q = 1) (hb : d77844 q = 1) : d79648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7244, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7245 q = 1) (hb : d77844 q = 1) : d79649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7245, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7246 q = 1) (hb : d77844 q = 1) : d79650 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7246, d79650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7246, d79650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7247 q = 1) (hb : d77844 q = 1) : d79651 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7247, d79651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7247, d79651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16432 (p : Pattern) (ha : d77845 p = 1) (hb : d85394 p = 1) : d79657 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d117 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8144 q ha hb
    | true =>
      simp only [d117, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d124 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8145 q ha hb
    | true =>
      simp only [d124, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d125 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d126 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d42 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d7248 q = 1) (hb : d77845 q = 1) : d79652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16431 q ha hb
    | true =>
      simp only [d7248, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d77845 q = 1) (hb : d85390 q = 1) : d79653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85390, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85390, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d43 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8133 q ha hb
    | true =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d44 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d77845 q = 1) (hb : d85391 q = 1) : d79654 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85391, d79654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85391, d79654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d77845 q = 1) (hb : d85392 q = 1) : d79655 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85392, d79655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d85392, d79655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85393 q = 1) : d79656 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85393, d79656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85393, d79656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77845 q = 1) (hb : d85394 q = 1) : d79657 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85394, d79657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85394, d79657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro16433 (p : Pattern) (ha : d7254 p = 1) (hb : d77844 p = 1) : d79658 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7243 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d38 q = 1) (hb : d77842 q = 1) : d38 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7244 q = 1) (hb : d77844 q = 1) : d79648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7244, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7245 q = 1) (hb : d77844 q = 1) : d79649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7245, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7246 q = 1) (hb : d77844 q = 1) : d79650 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7246, d79650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7246, d79650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7254 q = 1) (hb : d77844 q = 1) : d79658 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7254, d79658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7254, d79658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16434 (p : Pattern) (ha : d77845 p = 1) (hb : d85399 p = 1) : d79664 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d117 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d117, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8144 q ha hb
    | true =>
      simp only [d117, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d118 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d119 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d120 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d124 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d124, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8145 q ha hb
    | true =>
      simp only [d124, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d125 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d126 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d42 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d7248 q = 1) (hb : d77845 q = 1) : d79652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16431 q ha hb
    | true =>
      simp only [d7248, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d77845 q = 1) (hb : d85390 q = 1) : d79653 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85390, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d85390, d79653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d43 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8133 q ha hb
    | true =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h13 (q : Pattern) (ha : d44 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d44, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d77845 q = 1) (hb : d85391 q = 1) : d79654 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85391, d79654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85391, d79654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d77845 q = 1) (hb : d85392 q = 1) : d79655 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85392, d79655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d85392, d79655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85393 q = 1) : d79656 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85393, d79656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85393, d79656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d195 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d195, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8148 q ha hb
    | true =>
      simp only [d195, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h18 (q : Pattern) (ha : d196 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d197 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h20 (q : Pattern) (ha : d198 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d200 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d200, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8149 q ha hb
    | true =>
      simp only [d200, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h22 (q : Pattern) (ha : d201 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d202 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d49 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d7255 q = 1) (hb : d77845 q = 1) : d79659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d77845, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16433 q ha hb
    | true =>
      simp only [d7255, d77845, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d77845 q = 1) (hb : d85395 q = 1) : d79660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85395, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q hb ha
    | true =>
      simp only [d85395, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d50 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8135 q ha hb
    | true =>
      simp only [d50, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h28 (q : Pattern) (ha : d51 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h29 (q : Pattern) (ha : d77845 q = 1) (hb : d85396 q = 1) : d79661 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85396, d79661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d85396, d79661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d77845 q = 1) (hb : d85397 q = 1) : d79662 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85397, d79662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d85397, d79662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d77845 q = 1) (hb : d85398 q = 1) : d79663 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85398, d79663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q hb ha
    | true =>
      simp only [d85398, d79663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  have h32 (q : Pattern) (ha : d77845 q = 1) (hb : d85399 q = 1) : d79664 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85399, d79664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85399, d79664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
  exact h32 p ha hb
theorem andIntro16435 (p : Pattern) (ha : d77845 p = 1) (hb : d85406 p = 1) : d79669 p = 1 := by
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
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85395 q = 1) : d79660 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85395, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85395, d79660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d50 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d50, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8135 q ha hb
    | true =>
      simp only [d50, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d51 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d51, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d85396 q = 1) : d79661 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85396, d79661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85396, d79661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85404 q = 1) : d79662 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85404, d79662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85404, d79662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85405 q = 1) : d79663 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85405, d79663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85405, d79663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85406 q = 1) : d79669 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85406, d79669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85406, d79669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16436 (p : Pattern) (ha : d7280 p = 1) (hb : d77844 p = 1) : d79678 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7276 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d79 q = 1) (hb : d77842 q = 1) : d79 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7277 q = 1) (hb : d77844 q = 1) : d79675 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7277, d77844, d79675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7277, d77844, d79675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7278 q = 1) (hb : d77844 q = 1) : d79676 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7278, d79676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7278, d79676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7279 q = 1) (hb : d77844 q = 1) : d79677 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7279, d79677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7279, d79677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7280 q = 1) (hb : d77844 q = 1) : d79678 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7280, d79678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7280, d79678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16437 (p : Pattern) (ha : d77845 p = 1) (hb : d85416 p = 1) : d79684 p = 1 := by
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
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85412 q = 1) : d79680 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85412, d79680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85412, d79680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d84 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d84, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8138 q ha hb
    | true =>
      simp only [d84, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d85 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d85, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d85413 q = 1) : d79681 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85413, d79681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85413, d79681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85414 q = 1) : d79682 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85414, d79682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85414, d79682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85415 q = 1) : d79683 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85415, d79683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85415, d79683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85416 q = 1) : d79684 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85416, d79684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85416, d79684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16438 (p : Pattern) (ha : d77845 p = 1) (hb : d85422 p = 1) : d79690 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d105 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8141 q ha hb
  have h2 (q : Pattern) (ha : d106 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d112 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8141 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8142 q ha hb
  have h4 (q : Pattern) (ha : d113 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d114 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85400 q = 1) : d79665 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85400, d79665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16432 q ha hb
    | true =>
      simp only [d85400, d79665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16434 q ha hb
  have h7 (q : Pattern) (ha : d214 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8143 q ha hb
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85401 q = 1) : d79666 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85401, d79666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85401, d79666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85402 q = 1) : d79667 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85402, d79667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85402, d79667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85403 q = 1) : d79668 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85403, d79668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85403, d79668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77845 q = 1) (hb : d85407 q = 1) : d79670 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85407, d79670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85407, d79670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16435 q ha hb
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d85408 q = 1) : d79671 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85408, d79671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85408, d79671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d77845 q = 1) (hb : d85409 q = 1) : d79672 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85409, d79672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85409, d79672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d77845 q = 1) (hb : d85410 q = 1) : d79673 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85410, d79673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85410, d79673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d77845 q = 1) (hb : d85411 q = 1) : d79674 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85411, d79674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85411, d79674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85417 q = 1) : d79685 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85417, d79685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85417, d79685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16437 q ha hb
  have h17 (q : Pattern) (ha : d77845 q = 1) (hb : d85418 q = 1) : d79686 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85418, d79686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85418, d79686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d77845 q = 1) (hb : d85419 q = 1) : d79687 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85419, d79687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85419, d79687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d77845 q = 1) (hb : d85420 q = 1) : d79688 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85420, d79688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85420, d79688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d77845 q = 1) (hb : d85421 q = 1) : d79689 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85421, d79689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d85421, d79689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d77845 q = 1) (hb : d85422 q = 1) : d79690 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85422, d79690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d85422, d79690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro16439 (p : Pattern) (ha : d7302 p = 1) (hb : d77845 p = 1) : d79700 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7248 q = 1) (hb : d77845 q = 1) : d79652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16431 q ha hb
    | true =>
      simp only [d7248, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7298 q = 1) (hb : d77845 q = 1) : d79696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7299 q = 1) (hb : d77845 q = 1) : d79697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7299, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7300 q = 1) (hb : d77845 q = 1) : d79698 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7301 q = 1) (hb : d77845 q = 1) : d79699 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7302 q = 1) (hb : d77845 q = 1) : d79700 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7302, d79700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7302, d79700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16440 (p : Pattern) (ha : d7309 p = 1) (hb : d77845 p = 1) : d79707 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7248 q = 1) (hb : d77845 q = 1) : d79652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16431 q ha hb
    | true =>
      simp only [d7248, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7298 q = 1) (hb : d77845 q = 1) : d79696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7299 q = 1) (hb : d77845 q = 1) : d79697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7299, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7300 q = 1) (hb : d77845 q = 1) : d79698 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7301 q = 1) (hb : d77845 q = 1) : d79699 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d49 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7255 q = 1) (hb : d77845 q = 1) : d79659 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7255, d77845, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16433 q ha hb
    | true =>
      simp only [d7255, d77845, d79659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d7305 q = 1) (hb : d77845 q = 1) : d79703 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7305, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7305, d79703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7306 q = 1) (hb : d77845 q = 1) : d79704 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7306, d79704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7306, d79704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7307 q = 1) (hb : d77845 q = 1) : d79705 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7307, d79705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7307, d79705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d7308 q = 1) (hb : d77845 q = 1) : d79706 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7308, d79706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7308, d79706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7309 q = 1) (hb : d77845 q = 1) : d79707 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7309, d79707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7309, d79707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16441 (p : Pattern) (ha : d7376 p = 1) (hb : d77845 p = 1) : d110010 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d42 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7248 q = 1) (hb : d77845 q = 1) : d79652 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7248, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16431 q ha hb
    | true =>
      simp only [d7248, d77845, d79652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7298 q = 1) (hb : d77845 q = 1) : d79696 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7298, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7298, d79696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7299 q = 1) (hb : d77845 q = 1) : d79697 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7299, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7299, d79697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7300 q = 1) (hb : d77845 q = 1) : d79698 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7300, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7300, d79698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7301 q = 1) (hb : d77845 q = 1) : d79699 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7301, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7301, d79699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d43 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8133 q ha hb
    | true =>
      simp only [d43, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d100 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d101 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d102 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d103 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7376 q = 1) (hb : d77845 q = 1) : d110010 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7376, d110010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7376, d110010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16442 (p : Pattern) (ha : d7314 p = 1) (hb : d77844 p = 1) : d79712 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7243 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d77842 q = 1) : d38 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7244 q = 1) (hb : d77844 q = 1) : d79648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7244, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7245 q = 1) (hb : d77844 q = 1) : d79649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7245, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7313 q = 1) (hb : d77844 q = 1) : d79711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7313, d79711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7313, d79711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7314 q = 1) (hb : d77844 q = 1) : d79712 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7314, d79712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7314, d79712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16443 (p : Pattern) (ha : d7321 p = 1) (hb : d77844 p = 1) : d79719 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7243 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d77842 q = 1) : d38 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7244 q = 1) (hb : d77844 q = 1) : d79648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7244, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7319 q = 1) (hb : d77844 q = 1) : d79717 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7319, d79717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7319, d79717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7320 q = 1) (hb : d77844 q = 1) : d79718 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7320, d79718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7320, d79718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7321 q = 1) (hb : d77844 q = 1) : d79719 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7321, d79719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7321, d79719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16444 (p : Pattern) (ha : d7332 p = 1) (hb : d77844 p = 1) : d79726 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7243 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7329 q = 1) (hb : d77844 q = 1) : d79723 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7329, d77844, d79723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7329, d77844, d79723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7330 q = 1) (hb : d77844 q = 1) : d79724 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7330, d79724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7330, d79724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7331 q = 1) (hb : d77844 q = 1) : d79725 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7331, d79725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7331, d79725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7332 q = 1) (hb : d77844 q = 1) : d79726 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7332, d79726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7332, d79726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16445 (p : Pattern) (ha : d7347 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7243 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7344 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7344, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7345 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7346 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7347 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16446 (p : Pattern) (ha : d77845 p = 1) (hb : d85432 p = 1) : d110004 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7315 q = 1) (hb : d77845 q = 1) : d79713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7315, d77845, d79713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16442 q ha hb
    | true =>
      simp only [d7315, d77845, d79713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7316 q = 1) (hb : d77845 q = 1) : d79714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7316, d79714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7316, d79714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7317 q = 1) (hb : d77845 q = 1) : d79715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7317, d79715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7317, d79715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7318 q = 1) (hb : d77845 q = 1) : d79716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7318, d79716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7318, d79716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7322 q = 1) (hb : d77845 q = 1) : d79720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7322, d77845, d79720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16443 q ha hb
    | true =>
      simp only [d7322, d77845, d79720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d7323 q = 1) (hb : d77845 q = 1) : d79721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7323, d79721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7323, d79721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7324 q = 1) (hb : d77845 q = 1) : d79722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7324, d79722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7324, d79722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7247 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7333 q = 1) (hb : d77845 q = 1) : d79727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7333, d77845, d79727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16444 q ha hb
    | true =>
      simp only [d7333, d77845, d79727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d85428 q = 1) : d79728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85428, d79728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85428, d79728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d7348 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7348, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16445 q ha hb
    | true =>
      simp only [d7348, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d7349 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d7349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85429 q = 1) : d110001 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85429, d110001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85429, d110001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d77845 q = 1) (hb : d85430 q = 1) : d110002 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85430, d110002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85430, d110002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77845 q = 1) (hb : d85431 q = 1) : d110003 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85431, d110003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85431, d110003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d77845 q = 1) (hb : d85432 q = 1) : d110004 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85432, d110004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85432, d110004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro16447 (p : Pattern) (ha : d7354 p = 1) (hb : d77844 p = 1) : d79733 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7243 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d77842 q = 1) : d38 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7244 q = 1) (hb : d77844 q = 1) : d79648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7244, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7245 q = 1) (hb : d77844 q = 1) : d79649 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7245, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7245, d79649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7313 q = 1) (hb : d77844 q = 1) : d79711 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7313, d79711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7313, d79711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7354 q = 1) (hb : d77844 q = 1) : d79733 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7354, d79733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7354, d79733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16448 (p : Pattern) (ha : d7359 p = 1) (hb : d77844 p = 1) : d79738 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7243 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d38 q = 1) (hb : d77842 q = 1) : d38 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7244 q = 1) (hb : d77844 q = 1) : d79648 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7244, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7244, d77844, d79648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7319 q = 1) (hb : d77844 q = 1) : d79717 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7319, d79717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7319, d79717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7320 q = 1) (hb : d77844 q = 1) : d79718 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7320, d79718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7320, d79718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7359 q = 1) (hb : d77844 q = 1) : d79738 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7359, d79738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7359, d79738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16449 (p : Pattern) (ha : d7363 p = 1) (hb : d77844 p = 1) : d79742 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7328 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7243 q = 1) (hb : d77842 q = 1) : d7243 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7329 q = 1) (hb : d77844 q = 1) : d79723 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7329, d77844, d79723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7329, d77844, d79723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7330 q = 1) (hb : d77844 q = 1) : d79724 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7330, d79724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7330, d79724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7331 q = 1) (hb : d77844 q = 1) : d79725 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7331, d79725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7331, d79725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7363 q = 1) (hb : d77844 q = 1) : d79742 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7363, d79742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7363, d79742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16450 (p : Pattern) (ha : d7368 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7243 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7344 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7344, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7344, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7345 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7346 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7368 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16451 (p : Pattern) (ha : d77845 p = 1) (hb : d85437 p = 1) : d110008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d116 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7315 q = 1) (hb : d77845 q = 1) : d79713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7315, d77845, d79713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16442 q ha hb
    | true =>
      simp only [d7315, d77845, d79713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7316 q = 1) (hb : d77845 q = 1) : d79714 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7316, d79714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7316, d79714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7317 q = 1) (hb : d77845 q = 1) : d79715 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7317, d79715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7317, d79715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7318 q = 1) (hb : d77845 q = 1) : d79716 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7318, d79716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7318, d79716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d123 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7322 q = 1) (hb : d77845 q = 1) : d79720 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7322, d77845, d79720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16443 q ha hb
    | true =>
      simp only [d7322, d77845, d79720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d7323 q = 1) (hb : d77845 q = 1) : d79721 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7323, d79721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7323, d79721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7324 q = 1) (hb : d77845 q = 1) : d79722 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7324, d79722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7324, d79722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7247 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7333 q = 1) (hb : d77845 q = 1) : d79727 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7333, d77845, d79727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16444 q ha hb
    | true =>
      simp only [d7333, d77845, d79727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d85428 q = 1) : d79728 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85428, d79728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85428, d79728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d7348 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7348, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16445 q ha hb
    | true =>
      simp only [d7348, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d7349 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d7349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85429 q = 1) : d110001 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85429, d110001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85429, d110001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d77845 q = 1) (hb : d85430 q = 1) : d110002 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85430, d110002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85430, d110002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77845 q = 1) (hb : d85431 q = 1) : d110003 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85431, d110003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85431, d110003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d194 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d7355 q = 1) (hb : d77845 q = 1) : d79734 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7355, d77845, d79734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16447 q ha hb
    | true =>
      simp only [d7355, d77845, d79734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d7356 q = 1) (hb : d77845 q = 1) : d79735 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7356, d79735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7356, d79735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d7357 q = 1) (hb : d77845 q = 1) : d79736 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7357, d79736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d7357, d79736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d7358 q = 1) (hb : d77845 q = 1) : d79737 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7358, d79737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7358, d79737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d199 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d7360 q = 1) (hb : d77845 q = 1) : d79739 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7360, d77845, d79739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16448 q ha hb
    | true =>
      simp only [d7360, d77845, d79739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d7361 q = 1) (hb : d77845 q = 1) : d79740 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7361, d79740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7361, d79740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d7362 q = 1) (hb : d77845 q = 1) : d79741 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7362, d79741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d7362, d79741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d7254 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d7364 q = 1) (hb : d77845 q = 1) : d79743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7364, d77845, d79743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16449 q ha hb
    | true =>
      simp only [d7364, d77845, d79743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d77845 q = 1) (hb : d85433 q = 1) : d79744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85433, d79744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
    | true =>
      simp only [d85433, d79744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d7369 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7369, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16450 q ha hb
    | true =>
      simp only [d7369, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h32 (q : Pattern) (ha : d7370 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
    | true =>
      simp only [d7370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h33 (q : Pattern) (ha : d77845 q = 1) (hb : d85434 q = 1) : d110005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85434, d110005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d85434, d110005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q hb ha
  have h34 (q : Pattern) (ha : d77845 q = 1) (hb : d85435 q = 1) : d110006 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85435, d110006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
    | true =>
      simp only [d85435, d110006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d77845 q = 1) (hb : d85436 q = 1) : d110007 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85436, d110007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d85436, d110007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  have h36 (q : Pattern) (ha : d77845 q = 1) (hb : d85437 q = 1) : d110008 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85437, d110008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85437, d110008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h35 q ha hb
  exact h36 p ha hb
theorem andIntro16452 (p : Pattern) (ha : d77845 p = 1) (hb : d85444 p = 1) : d110017 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7254 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7364 q = 1) (hb : d77845 q = 1) : d79743 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7364, d77845, d79743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16449 q ha hb
    | true =>
      simp only [d7364, d77845, d79743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85433 q = 1) : d79744 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85433, d79744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85433, d79744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7369 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7369, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16450 q ha hb
    | true =>
      simp only [d7369, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7370 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d85434 q = 1) : d110005 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85434, d110005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85434, d110005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85442 q = 1) : d110015 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85442, d110015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85442, d110015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85443 q = 1) : d110016 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85443, d110016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85443, d110016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85444 q = 1) : d110017 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85444, d110017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85444, d110017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16453 (p : Pattern) (ha : d7396 p = 1) (hb : d77844 p = 1) : d79764 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7392 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7276 q = 1) (hb : d77842 q = 1) : d7276 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7393 q = 1) (hb : d77844 q = 1) : d79761 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7393, d77844, d79761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7393, d77844, d79761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7394 q = 1) (hb : d77844 q = 1) : d79762 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7394, d79762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7394, d79762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7395 q = 1) (hb : d77844 q = 1) : d79763 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7395, d79763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7395, d79763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7396 q = 1) (hb : d77844 q = 1) : d79764 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7396, d79764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7396, d79764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16454 (p : Pattern) (ha : d7411 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7276 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7408 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7408, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7408, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7409 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7410 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7411 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16455 (p : Pattern) (ha : d77845 p = 1) (hb : d85454 p = 1) : d110026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7280 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7397 q = 1) (hb : d77845 q = 1) : d79765 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7397, d77845, d79765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16453 q ha hb
    | true =>
      simp only [d7397, d77845, d79765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85450 q = 1) : d79766 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85450, d79766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85450, d79766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7412 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7412, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16454 q ha hb
    | true =>
      simp only [d7412, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7413 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d85451 q = 1) : d110023 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85451, d110023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85451, d110023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85452 q = 1) : d110024 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85452, d110024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85452, d110024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85453 q = 1) : d110025 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85453, d110025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85453, d110025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85454 q = 1) : d110026 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85454, d110026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85454, d110026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16456 (p : Pattern) (ha : d77845 p = 1) (hb : d85460 p = 1) : d110032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7303 q = 1) (hb : d77845 q = 1) : d79701 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7303, d79701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7303, d79701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16439 q ha hb
  have h2 (q : Pattern) (ha : d7304 q = 1) (hb : d77845 q = 1) : d79702 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7304, d79702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7304, d79702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7310 q = 1) (hb : d77845 q = 1) : d79708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7310, d79708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16439 q ha hb
    | true =>
      simp only [d7310, d79708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16440 q ha hb
  have h4 (q : Pattern) (ha : d7311 q = 1) (hb : d77845 q = 1) : d79709 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7311, d79709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7311, d79709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7312 q = 1) (hb : d77845 q = 1) : d79710 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7312, d79710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7312, d79710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85438 q = 1) : d110009 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85438, d110009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16446 q ha hb
    | true =>
      simp only [d85438, d110009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16451 q ha hb
  have h7 (q : Pattern) (ha : d7377 q = 1) (hb : d77845 q = 1) : d110011 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7377, d110011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16441 q ha hb
    | true =>
      simp only [d7377, d110011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8142 q ha hb
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85439 q = 1) : d110012 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85439, d110012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85439, d110012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85440 q = 1) : d110013 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85440, d110013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85440, d110013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85441 q = 1) : d110014 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85441, d110014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85441, d110014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77845 q = 1) (hb : d85445 q = 1) : d110018 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85445, d110018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85445, d110018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16452 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8156 q ha hb
  have h13 (q : Pattern) (ha : d77845 q = 1) (hb : d85446 q = 1) : d110019 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85446, d110019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85446, d110019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d77845 q = 1) (hb : d85447 q = 1) : d110020 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85447, d110020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85447, d110020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d77845 q = 1) (hb : d85448 q = 1) : d110021 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85448, d110021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85448, d110021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85449 q = 1) : d110022 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85449, d110022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85449, d110022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77845 q = 1) (hb : d85455 q = 1) : d110027 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85455, d110027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85455, d110027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16455 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8157 q ha hb
  have h19 (q : Pattern) (ha : d77845 q = 1) (hb : d85456 q = 1) : d110028 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85456, d110028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85456, d110028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d77845 q = 1) (hb : d85457 q = 1) : d110029 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85457, d110029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d85457, d110029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d77845 q = 1) (hb : d85458 q = 1) : d110030 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85458, d110030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85458, d110030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d77845 q = 1) (hb : d85459 q = 1) : d110031 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85459, d110031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85459, d110031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d77845 q = 1) (hb : d85460 q = 1) : d110032 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85460, d110032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85460, d110032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro16457 (p : Pattern) (ha : d77845 p = 1) (hb : d85466 p = 1) : d110038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8140 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d85423 q = 1) : d79691 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85423, d79691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85423, d79691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16438 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85424 q = 1) : d79692 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85424, d79692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85424, d79692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d85425 q = 1) : d79693 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85425, d79693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85425, d79693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85426 q = 1) : d79694 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85426, d79694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85426, d79694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85427 q = 1) : d79695 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85427, d79695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d85427, d79695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85461 q = 1) : d110033 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85461, d110033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85461, d110033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16456 q ha hb
  have h11 (q : Pattern) (ha : d77845 q = 1) (hb : d85462 q = 1) : d110034 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85462, d110034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85462, d110034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d85463 q = 1) : d110035 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85463, d110035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85463, d110035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d77845 q = 1) (hb : d85464 q = 1) : d110036 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85464, d110036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85464, d110036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d77845 q = 1) (hb : d85465 q = 1) : d110037 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85465, d110037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85465, d110037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d77845 q = 1) (hb : d85466 q = 1) : d110038 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85466, d110038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d85466, d110038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro16458 (p : Pattern) (ha : d7433 p = 1) (hb : d77844 p = 1) : d79786 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d77842 q = 1) : d483 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7430 q = 1) (hb : d77844 q = 1) : d79783 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7430, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7431 q = 1) (hb : d77844 q = 1) : d79784 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7431, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7432 q = 1) (hb : d77844 q = 1) : d79785 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7432, d79785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7432, d79785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7433 q = 1) (hb : d77844 q = 1) : d79786 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7433, d79786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7433, d79786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16459 (p : Pattern) (ha : d7439 p = 1) (hb : d77845 p = 1) : d79792 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d491 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7434 q = 1) (hb : d77845 q = 1) : d79787 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d77845, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16458 q ha hb
    | true =>
      simp only [d7434, d77845, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7435 q = 1) (hb : d77845 q = 1) : d79788 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7436 q = 1) (hb : d77845 q = 1) : d79789 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7436, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7437 q = 1) (hb : d77845 q = 1) : d79790 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7438 q = 1) (hb : d77845 q = 1) : d79791 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7439 q = 1) (hb : d77845 q = 1) : d79792 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7439, d79792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7439, d79792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16460 (p : Pattern) (ha : d7442 p = 1) (hb : d77844 p = 1) : d79795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7328 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d483 q = 1) (hb : d77842 q = 1) : d483 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7430 q = 1) (hb : d77844 q = 1) : d79783 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7430, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7431 q = 1) (hb : d77844 q = 1) : d79784 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7431, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7432 q = 1) (hb : d77844 q = 1) : d79785 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7432, d79785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7432, d79785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7442 q = 1) (hb : d77844 q = 1) : d79795 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7442, d79795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7442, d79795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16461 (p : Pattern) (ha : d7448 p = 1) (hb : d77845 p = 1) : d79801 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d491 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7434 q = 1) (hb : d77845 q = 1) : d79787 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d77845, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16458 q ha hb
    | true =>
      simp only [d7434, d77845, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7435 q = 1) (hb : d77845 q = 1) : d79788 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7436 q = 1) (hb : d77845 q = 1) : d79789 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7436, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7437 q = 1) (hb : d77845 q = 1) : d79790 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7438 q = 1) (hb : d77845 q = 1) : d79791 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d501 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7443 q = 1) (hb : d77845 q = 1) : d79796 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7443, d77845, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16460 q ha hb
    | true =>
      simp only [d7443, d77845, d79796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d7444 q = 1) (hb : d77845 q = 1) : d79797 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7444, d79797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7444, d79797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7445 q = 1) (hb : d77845 q = 1) : d79798 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7445, d79798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7445, d79798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7446 q = 1) (hb : d77845 q = 1) : d79799 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7446, d79799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7446, d79799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d7447 q = 1) (hb : d77845 q = 1) : d79800 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7447, d79800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7447, d79800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7448 q = 1) (hb : d77845 q = 1) : d79801 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7448, d79801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7448, d79801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16462 (p : Pattern) (ha : d7515 p = 1) (hb : d77845 p = 1) : d110048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d491 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7434 q = 1) (hb : d77845 q = 1) : d79787 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7434, d77845, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16458 q ha hb
    | true =>
      simp only [d7434, d77845, d79787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7435 q = 1) (hb : d77845 q = 1) : d79788 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7435, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7435, d79788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7436 q = 1) (hb : d77845 q = 1) : d79789 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7436, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7436, d79789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7437 q = 1) (hb : d77845 q = 1) : d79790 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7437, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7437, d79790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7438 q = 1) (hb : d77845 q = 1) : d79791 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7438, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7438, d79791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d633 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d633, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8177 q ha hb
    | true =>
      simp only [d633, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d634 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d635 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d636 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d637 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7515 q = 1) (hb : d77845 q = 1) : d110048 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7515, d110048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7515, d110048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16463 (p : Pattern) (ha : d7453 p = 1) (hb : d77844 p = 1) : d79806 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d77842 q = 1) : d483 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7430 q = 1) (hb : d77844 q = 1) : d79783 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7430, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7431 q = 1) (hb : d77844 q = 1) : d79784 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7431, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7452 q = 1) (hb : d77844 q = 1) : d79805 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7452, d79805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7452, d79805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7453 q = 1) (hb : d77844 q = 1) : d79806 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7453, d79806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7453, d79806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16464 (p : Pattern) (ha : d7460 p = 1) (hb : d77844 p = 1) : d79813 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d77842 q = 1) : d483 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7430 q = 1) (hb : d77844 q = 1) : d79783 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7430, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7458 q = 1) (hb : d77844 q = 1) : d79811 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7458, d79811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7458, d79811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7459 q = 1) (hb : d77844 q = 1) : d79812 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7459, d79812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7459, d79812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7460 q = 1) (hb : d77844 q = 1) : d79813 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7460, d79813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7460, d79813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16465 (p : Pattern) (ha : d7471 p = 1) (hb : d77844 p = 1) : d79820 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7467 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7328 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7468 q = 1) (hb : d77844 q = 1) : d79817 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7468, d77844, d79817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7468, d77844, d79817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7469 q = 1) (hb : d77844 q = 1) : d79818 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7469, d79818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7469, d79818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7470 q = 1) (hb : d77844 q = 1) : d79819 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7470, d79819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7470, d79819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7471 q = 1) (hb : d77844 q = 1) : d79820 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7471, d79820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7471, d79820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16466 (p : Pattern) (ha : d7486 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7483 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7483, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7484 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7485 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7486 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16467 (p : Pattern) (ha : d77845 p = 1) (hb : d85471 p = 1) : d110042 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d514 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7454 q = 1) (hb : d77845 q = 1) : d79807 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7454, d77845, d79807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16463 q ha hb
    | true =>
      simp only [d7454, d77845, d79807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7455 q = 1) (hb : d77845 q = 1) : d79808 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7455, d79808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7455, d79808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7456 q = 1) (hb : d77845 q = 1) : d79809 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7456, d79809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7456, d79809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7457 q = 1) (hb : d77845 q = 1) : d79810 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7457, d79810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7457, d79810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d524 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7461 q = 1) (hb : d77845 q = 1) : d79814 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7461, d77845, d79814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16464 q ha hb
    | true =>
      simp only [d7461, d77845, d79814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d7462 q = 1) (hb : d77845 q = 1) : d79815 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7462, d79815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7462, d79815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7463 q = 1) (hb : d77845 q = 1) : d79816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7463, d79816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7463, d79816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7433 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7472 q = 1) (hb : d77845 q = 1) : d79821 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7472, d77845, d79821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16465 q ha hb
    | true =>
      simp only [d7472, d77845, d79821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d85467 q = 1) : d79822 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85467, d79822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85467, d79822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d7487 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7487, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16466 q ha hb
    | true =>
      simp only [d7487, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d7488 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d7488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85468 q = 1) : d110039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85468, d110039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85468, d110039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d77845 q = 1) (hb : d85469 q = 1) : d110040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85469, d110040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85469, d110040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77845 q = 1) (hb : d85470 q = 1) : d110041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85470, d110041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85470, d110041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d77845 q = 1) (hb : d85471 q = 1) : d110042 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85471, d110042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85471, d110042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro16468 (p : Pattern) (ha : d7493 p = 1) (hb : d77844 p = 1) : d79828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d77842 q = 1) : d483 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7430 q = 1) (hb : d77844 q = 1) : d79783 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7430, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7431 q = 1) (hb : d77844 q = 1) : d79784 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7431, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7431, d79784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7452 q = 1) (hb : d77844 q = 1) : d79805 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7452, d79805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7452, d79805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7493 q = 1) (hb : d77844 q = 1) : d79828 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7493, d79828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7493, d79828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16469 (p : Pattern) (ha : d7498 p = 1) (hb : d77844 p = 1) : d79833 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7328 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d483 q = 1) (hb : d77842 q = 1) : d483 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7430 q = 1) (hb : d77844 q = 1) : d79783 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7430, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7430, d77844, d79783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7458 q = 1) (hb : d77844 q = 1) : d79811 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7458, d79811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7458, d79811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7459 q = 1) (hb : d77844 q = 1) : d79812 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7459, d79812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7459, d79812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7498 q = 1) (hb : d77844 q = 1) : d79833 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7498, d79833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7498, d79833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16470 (p : Pattern) (ha : d7502 p = 1) (hb : d77844 p = 1) : d79837 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7467 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7328 q = 1) (hb : d77842 q = 1) : d7328 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7468 q = 1) (hb : d77844 q = 1) : d79817 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7468, d77844, d79817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7468, d77844, d79817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7469 q = 1) (hb : d77844 q = 1) : d79818 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7469, d79818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7469, d79818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7470 q = 1) (hb : d77844 q = 1) : d79819 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7470, d79819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7470, d79819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7502 q = 1) (hb : d77844 q = 1) : d79837 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7502, d79837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7502, d79837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16471 (p : Pattern) (ha : d7507 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7328 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7483 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7483, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7483, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7484 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7485 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7507 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16472 (p : Pattern) (ha : d77845 p = 1) (hb : d85476 p = 1) : d110046 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d514 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7454 q = 1) (hb : d77845 q = 1) : d79807 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7454, d77845, d79807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16463 q ha hb
    | true =>
      simp only [d7454, d77845, d79807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7455 q = 1) (hb : d77845 q = 1) : d79808 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7455, d79808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7455, d79808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7456 q = 1) (hb : d77845 q = 1) : d79809 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7456, d79809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7456, d79809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7457 q = 1) (hb : d77845 q = 1) : d79810 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7457, d79810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7457, d79810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d524 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7461 q = 1) (hb : d77845 q = 1) : d79814 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7461, d77845, d79814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16464 q ha hb
    | true =>
      simp only [d7461, d77845, d79814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d7462 q = 1) (hb : d77845 q = 1) : d79815 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7462, d79815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7462, d79815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7463 q = 1) (hb : d77845 q = 1) : d79816 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7463, d79816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7463, d79816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7433 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7472 q = 1) (hb : d77845 q = 1) : d79821 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7472, d77845, d79821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16465 q ha hb
    | true =>
      simp only [d7472, d77845, d79821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d85467 q = 1) : d79822 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85467, d79822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85467, d79822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d7487 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7487, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16466 q ha hb
    | true =>
      simp only [d7487, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d7488 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d7488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85468 q = 1) : d110039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85468, d110039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85468, d110039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d77845 q = 1) (hb : d85469 q = 1) : d110040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85469, d110040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85469, d110040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77845 q = 1) (hb : d85470 q = 1) : d110041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85470, d110041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85470, d110041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d610 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d7494 q = 1) (hb : d77845 q = 1) : d79829 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7494, d77845, d79829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16468 q ha hb
    | true =>
      simp only [d7494, d77845, d79829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d7495 q = 1) (hb : d77845 q = 1) : d79830 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7495, d79830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7495, d79830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d7496 q = 1) (hb : d77845 q = 1) : d79831 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7496, d79831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d7496, d79831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d7497 q = 1) (hb : d77845 q = 1) : d79832 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7497, d79832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7497, d79832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d616 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d7499 q = 1) (hb : d77845 q = 1) : d79834 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7499, d77845, d79834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16469 q ha hb
    | true =>
      simp only [d7499, d77845, d79834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d7500 q = 1) (hb : d77845 q = 1) : d79835 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7500, d79835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7500, d79835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d7501 q = 1) (hb : d77845 q = 1) : d79836 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7501, d79836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d7501, d79836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d7442 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d7503 q = 1) (hb : d77845 q = 1) : d79838 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7503, d77845, d79838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16470 q ha hb
    | true =>
      simp only [d7503, d77845, d79838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d77845 q = 1) (hb : d85472 q = 1) : d79839 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85472, d79839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
    | true =>
      simp only [d85472, d79839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d7508 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7508, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16471 q ha hb
    | true =>
      simp only [d7508, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h32 (q : Pattern) (ha : d7509 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
    | true =>
      simp only [d7509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h33 (q : Pattern) (ha : d77845 q = 1) (hb : d85473 q = 1) : d110043 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85473, d110043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d85473, d110043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q hb ha
  have h34 (q : Pattern) (ha : d77845 q = 1) (hb : d85474 q = 1) : d110044 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85474, d110044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
    | true =>
      simp only [d85474, d110044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d77845 q = 1) (hb : d85475 q = 1) : d110045 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85475, d110045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d85475, d110045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  have h36 (q : Pattern) (ha : d77845 q = 1) (hb : d85476 q = 1) : d110046 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85476, d110046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85476, d110046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h35 q ha hb
  exact h36 p ha hb
theorem andIntro16473 (p : Pattern) (ha : d77845 p = 1) (hb : d85483 p = 1) : d110055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7442 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7503 q = 1) (hb : d77845 q = 1) : d79838 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7503, d77845, d79838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16470 q ha hb
    | true =>
      simp only [d7503, d77845, d79838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85472 q = 1) : d79839 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85472, d79839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85472, d79839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7508 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7508, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16471 q ha hb
    | true =>
      simp only [d7508, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7509 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d85473 q = 1) : d110043 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85473, d110043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85473, d110043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85481 q = 1) : d110053 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85481, d110053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85481, d110053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85482 q = 1) : d110054 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85482, d110054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85482, d110054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85483 q = 1) : d110055 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85483, d110055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85483, d110055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16474 (p : Pattern) (ha : d7535 p = 1) (hb : d77844 p = 1) : d79860 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7531 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7392 q = 1) (hb : d77842 q = 1) : d7392 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7532 q = 1) (hb : d77844 q = 1) : d79857 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7532, d77844, d79857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7532, d77844, d79857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7533 q = 1) (hb : d77844 q = 1) : d79858 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7533, d79858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7533, d79858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7534 q = 1) (hb : d77844 q = 1) : d79859 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7534, d79859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7534, d79859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7535 q = 1) (hb : d77844 q = 1) : d79860 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7535, d79860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7535, d79860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16475 (p : Pattern) (ha : d7554 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7392 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7551 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7551, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7551, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7552 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7553 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7554 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16476 (p : Pattern) (ha : d77845 p = 1) (hb : d85493 p = 1) : d110064 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7539 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7540 q = 1) (hb : d77845 q = 1) : d79861 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7540, d77845, d79861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16474 q ha hb
    | true =>
      simp only [d7540, d77845, d79861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85489 q = 1) : d79862 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85489, d79862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85489, d79862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7555 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7555, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16475 q ha hb
    | true =>
      simp only [d7555, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7556 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d85490 q = 1) : d110061 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85490, d110061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85490, d110061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85491 q = 1) : d110062 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85491, d110062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85491, d110062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85492 q = 1) : d110063 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85492, d110063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85492, d110063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85493 q = 1) : d110064 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85493, d110064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85493, d110064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16477 (p : Pattern) (ha : d77845 p = 1) (hb : d85499 p = 1) : d110070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7440 q = 1) (hb : d77845 q = 1) : d79793 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7440, d79793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7440, d79793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16459 q ha hb
  have h2 (q : Pattern) (ha : d7441 q = 1) (hb : d77845 q = 1) : d79794 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7441, d79794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7441, d79794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7449 q = 1) (hb : d77845 q = 1) : d79802 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7449, d79802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16459 q ha hb
    | true =>
      simp only [d7449, d79802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16461 q ha hb
  have h4 (q : Pattern) (ha : d7450 q = 1) (hb : d77845 q = 1) : d79803 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7450, d79803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7450, d79803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7451 q = 1) (hb : d77845 q = 1) : d79804 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7451, d79804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7451, d79804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85477 q = 1) : d110047 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85477, d110047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16467 q ha hb
    | true =>
      simp only [d85477, d110047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16472 q ha hb
  have h7 (q : Pattern) (ha : d7516 q = 1) (hb : d77845 q = 1) : d110049 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7516, d110049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16462 q ha hb
    | true =>
      simp only [d7516, d110049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8179 q ha hb
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85478 q = 1) : d110050 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85478, d110050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85478, d110050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85479 q = 1) : d110051 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85479, d110051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85479, d110051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85480 q = 1) : d110052 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85480, d110052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85480, d110052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77845 q = 1) (hb : d85484 q = 1) : d110056 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85484, d110056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85484, d110056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16473 q ha hb
  have h12 (q : Pattern) (ha : d654 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8180 q ha hb
  have h13 (q : Pattern) (ha : d77845 q = 1) (hb : d85485 q = 1) : d110057 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85485, d110057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85485, d110057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d77845 q = 1) (hb : d85486 q = 1) : d110058 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85486, d110058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85486, d110058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d77845 q = 1) (hb : d85487 q = 1) : d110059 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85487, d110059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85487, d110059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85488 q = 1) : d110060 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85488, d110060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85488, d110060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77845 q = 1) (hb : d85494 q = 1) : d110065 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85494, d110065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85494, d110065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16476 q ha hb
  have h18 (q : Pattern) (ha : d737 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8182 q ha hb
  have h19 (q : Pattern) (ha : d77845 q = 1) (hb : d85495 q = 1) : d110066 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85495, d110066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85495, d110066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d77845 q = 1) (hb : d85496 q = 1) : d110067 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85496, d110067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d85496, d110067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d77845 q = 1) (hb : d85497 q = 1) : d110068 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85497, d110068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85497, d110068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d77845 q = 1) (hb : d85498 q = 1) : d110069 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85498, d110069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85498, d110069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d77845 q = 1) (hb : d85499 q = 1) : d110070 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85499, d110070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85499, d110070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro16478 (p : Pattern) (ha : d77845 p = 1) (hb : d85505 p = 1) : d110076 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d85500 q = 1) : d110071 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85500, d110071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85500, d110071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16477 q ha hb
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d85501 q = 1) : d110072 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85501, d110072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85501, d110072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85502 q = 1) : d110073 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85502, d110073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85502, d110073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d85503 q = 1) : d110074 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85503, d110074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85503, d110074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d85504 q = 1) : d110075 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85504, d110075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85504, d110075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85505 q = 1) : d110076 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85505, d110076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85505, d110076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16479 (p : Pattern) (ha : d7581 p = 1) (hb : d77844 p = 1) : d79889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7577 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d77842 q = 1) : d775 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7578 q = 1) (hb : d77844 q = 1) : d79886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7578, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7579 q = 1) (hb : d77844 q = 1) : d79887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7579, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7580 q = 1) (hb : d77844 q = 1) : d79888 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7580, d79888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7580, d79888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7581 q = 1) (hb : d77844 q = 1) : d79889 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7581, d79889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7581, d79889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16480 (p : Pattern) (ha : d7587 p = 1) (hb : d77845 p = 1) : d79895 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d783 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7582 q = 1) (hb : d77845 q = 1) : d79890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d77845, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16479 q ha hb
    | true =>
      simp only [d7582, d77845, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7583 q = 1) (hb : d77845 q = 1) : d79891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7584 q = 1) (hb : d77845 q = 1) : d79892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7584, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7585 q = 1) (hb : d77845 q = 1) : d79893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7586 q = 1) (hb : d77845 q = 1) : d79894 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d7587 q = 1) (hb : d77845 q = 1) : d79895 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7587, d79895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7587, d79895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro16481 (p : Pattern) (ha : d7590 p = 1) (hb : d77844 p = 1) : d79898 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7577 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d775 q = 1) (hb : d77842 q = 1) : d775 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7578 q = 1) (hb : d77844 q = 1) : d79886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7578, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7579 q = 1) (hb : d77844 q = 1) : d79887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7579, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7580 q = 1) (hb : d77844 q = 1) : d79888 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7580, d79888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7580, d79888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7590 q = 1) (hb : d77844 q = 1) : d79898 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7590, d79898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7590, d79898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16482 (p : Pattern) (ha : d7596 p = 1) (hb : d77845 p = 1) : d79904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d783 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7582 q = 1) (hb : d77845 q = 1) : d79890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d77845, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16479 q ha hb
    | true =>
      simp only [d7582, d77845, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7583 q = 1) (hb : d77845 q = 1) : d79891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7584 q = 1) (hb : d77845 q = 1) : d79892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7584, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7585 q = 1) (hb : d77845 q = 1) : d79893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7586 q = 1) (hb : d77845 q = 1) : d79894 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d793 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d7591 q = 1) (hb : d77845 q = 1) : d79899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7591, d77845, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16481 q ha hb
    | true =>
      simp only [d7591, d77845, d79899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d7592 q = 1) (hb : d77845 q = 1) : d79900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7592, d79900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7592, d79900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d7593 q = 1) (hb : d77845 q = 1) : d79901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7593, d79901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d7593, d79901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d7594 q = 1) (hb : d77845 q = 1) : d79902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7594, d79902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7594, d79902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d7595 q = 1) (hb : d77845 q = 1) : d79903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7595, d79903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7595, d79903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7596 q = 1) (hb : d77845 q = 1) : d79904 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7596, d79904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7596, d79904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16483 (p : Pattern) (ha : d7663 p = 1) (hb : d77845 p = 1) : d110087 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d783 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7582 q = 1) (hb : d77845 q = 1) : d79890 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7582, d77845, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16479 q ha hb
    | true =>
      simp only [d7582, d77845, d79890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7583 q = 1) (hb : d77845 q = 1) : d79891 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7583, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7583, d79891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7584 q = 1) (hb : d77845 q = 1) : d79892 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7584, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7584, d79892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7585 q = 1) (hb : d77845 q = 1) : d79893 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7585, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7585, d79893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7586 q = 1) (hb : d77845 q = 1) : d79894 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d7586, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7586, d79894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d939 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d939, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8205 q ha hb
    | true =>
      simp only [d939, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d940 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d941 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d942 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d943 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d7663 q = 1) (hb : d77845 q = 1) : d110087 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d7663, d110087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d7663, d110087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro16484 (p : Pattern) (ha : d7601 p = 1) (hb : d77844 p = 1) : d79909 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7577 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d77842 q = 1) : d775 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7578 q = 1) (hb : d77844 q = 1) : d79886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7578, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7579 q = 1) (hb : d77844 q = 1) : d79887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7579, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7600 q = 1) (hb : d77844 q = 1) : d79908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7600, d79908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7600, d79908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7601 q = 1) (hb : d77844 q = 1) : d79909 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7601, d79909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7601, d79909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16485 (p : Pattern) (ha : d7608 p = 1) (hb : d77844 p = 1) : d79916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7577 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d77842 q = 1) : d775 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7578 q = 1) (hb : d77844 q = 1) : d79886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7578, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7606 q = 1) (hb : d77844 q = 1) : d79914 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7606, d79914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7606, d79914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7607 q = 1) (hb : d77844 q = 1) : d79915 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7607, d79915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7607, d79915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7608 q = 1) (hb : d77844 q = 1) : d79916 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7608, d79916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7608, d79916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16486 (p : Pattern) (ha : d7619 p = 1) (hb : d77844 p = 1) : d79923 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7615 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7577 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7616 q = 1) (hb : d77844 q = 1) : d79920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7616, d77844, d79920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7616, d77844, d79920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7617 q = 1) (hb : d77844 q = 1) : d79921 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7617, d79921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7617, d79921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7618 q = 1) (hb : d77844 q = 1) : d79922 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7618, d79922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7618, d79922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7619 q = 1) (hb : d77844 q = 1) : d79923 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7619, d79923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7619, d79923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16487 (p : Pattern) (ha : d7634 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7577 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7631 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7631, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7631, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7632 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7633 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7634 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro16488 (p : Pattern) (ha : d77845 p = 1) (hb : d85511 p = 1) : d110081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d806 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7602 q = 1) (hb : d77845 q = 1) : d79910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7602, d77845, d79910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16484 q ha hb
    | true =>
      simp only [d7602, d77845, d79910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7603 q = 1) (hb : d77845 q = 1) : d79911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7603, d79911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7603, d79911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7604 q = 1) (hb : d77845 q = 1) : d79912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7604, d79912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7604, d79912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7605 q = 1) (hb : d77845 q = 1) : d79913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7605, d79913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7605, d79913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d816 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7609 q = 1) (hb : d77845 q = 1) : d79917 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7609, d77845, d79917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16485 q ha hb
    | true =>
      simp only [d7609, d77845, d79917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d7610 q = 1) (hb : d77845 q = 1) : d79918 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7610, d79918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7610, d79918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7611 q = 1) (hb : d77845 q = 1) : d79919 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7611, d79919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7611, d79919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7581 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7620 q = 1) (hb : d77845 q = 1) : d79924 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7620, d77845, d79924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16486 q ha hb
    | true =>
      simp only [d7620, d77845, d79924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d85507 q = 1) : d79925 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85507, d79925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85507, d79925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d7635 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7635, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16487 q ha hb
    | true =>
      simp only [d7635, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d7636 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d7636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85508 q = 1) : d110078 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85508, d110078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85508, d110078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d77845 q = 1) (hb : d85509 q = 1) : d110079 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85509, d110079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85509, d110079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77845 q = 1) (hb : d85510 q = 1) : d110080 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85510, d110080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85510, d110080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d77845 q = 1) (hb : d85511 q = 1) : d110081 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85511, d110081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85511, d110081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro16489 (p : Pattern) (ha : d7641 p = 1) (hb : d77844 p = 1) : d79931 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7577 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d77842 q = 1) : d775 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7578 q = 1) (hb : d77844 q = 1) : d79886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7578, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7579 q = 1) (hb : d77844 q = 1) : d79887 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7579, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7579, d79887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7600 q = 1) (hb : d77844 q = 1) : d79908 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7600, d79908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7600, d79908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7641 q = 1) (hb : d77844 q = 1) : d79931 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7641, d79931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7641, d79931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16490 (p : Pattern) (ha : d7646 p = 1) (hb : d77844 p = 1) : d79936 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7577 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d77842 q = 1) : d775 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d7578 q = 1) (hb : d77844 q = 1) : d79886 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7578, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d7578, d77844, d79886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7606 q = 1) (hb : d77844 q = 1) : d79914 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7606, d79914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7606, d79914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7607 q = 1) (hb : d77844 q = 1) : d79915 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7607, d79915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7607, d79915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d7646 q = 1) (hb : d77844 q = 1) : d79936 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7646, d79936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7646, d79936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro16491 (p : Pattern) (ha : d7650 p = 1) (hb : d77844 p = 1) : d79940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7615 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7577 q = 1) (hb : d77842 q = 1) : d7577 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7616 q = 1) (hb : d77844 q = 1) : d79920 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7616, d77844, d79920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7616, d77844, d79920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7617 q = 1) (hb : d77844 q = 1) : d79921 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7617, d79921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7617, d79921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7618 q = 1) (hb : d77844 q = 1) : d79922 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7618, d79922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7618, d79922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7650 q = 1) (hb : d77844 q = 1) : d79940 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7650, d79940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7650, d79940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16492 (p : Pattern) (ha : d7655 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7577 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7631 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7631, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7631, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7632 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7633 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7655 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16493 (p : Pattern) (ha : d77845 p = 1) (hb : d85516 p = 1) : d110085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d806 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7602 q = 1) (hb : d77845 q = 1) : d79910 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7602, d77845, d79910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16484 q ha hb
    | true =>
      simp only [d7602, d77845, d79910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d7603 q = 1) (hb : d77845 q = 1) : d79911 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7603, d79911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7603, d79911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d7604 q = 1) (hb : d77845 q = 1) : d79912 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7604, d79912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7604, d79912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7605 q = 1) (hb : d77845 q = 1) : d79913 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7605, d79913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7605, d79913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d816 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d7609 q = 1) (hb : d77845 q = 1) : d79917 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7609, d77845, d79917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16485 q ha hb
    | true =>
      simp only [d7609, d77845, d79917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d7610 q = 1) (hb : d77845 q = 1) : d79918 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7610, d79918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7610, d79918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d7611 q = 1) (hb : d77845 q = 1) : d79919 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7611, d79919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d7611, d79919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d7581 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d7620 q = 1) (hb : d77845 q = 1) : d79924 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7620, d77845, d79924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16486 q ha hb
    | true =>
      simp only [d7620, d77845, d79924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d77845 q = 1) (hb : d85507 q = 1) : d79925 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85507, d79925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d85507, d79925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d7635 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7635, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16487 q ha hb
    | true =>
      simp only [d7635, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d7636 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d7636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85508 q = 1) : d110078 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85508, d110078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d85508, d110078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d77845 q = 1) (hb : d85509 q = 1) : d110079 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85509, d110079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d85509, d110079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d77845 q = 1) (hb : d85510 q = 1) : d110080 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85510, d110080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85510, d110080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d0 q = 1) (hb : d916 q = 1) : d0 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d7642 q = 1) (hb : d77845 q = 1) : d79932 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7642, d77845, d79932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16489 q ha hb
    | true =>
      simp only [d7642, d77845, d79932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
  have h21 (q : Pattern) (ha : d7643 q = 1) (hb : d77845 q = 1) : d79933 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7643, d79933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7643, d79933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d7644 q = 1) (hb : d77845 q = 1) : d79934 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7644, d79934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d7644, d79934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d7645 q = 1) (hb : d77845 q = 1) : d79935 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d7645, d79935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7645, d79935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d922 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d7647 q = 1) (hb : d77845 q = 1) : d79937 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7647, d77845, d79937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16490 q ha hb
    | true =>
      simp only [d7647, d77845, d79937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d7648 q = 1) (hb : d77845 q = 1) : d79938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7648, d79938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7648, d79938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d7649 q = 1) (hb : d77845 q = 1) : d79939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d7649, d79939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d7649, d79939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d0 q = 1) (hb : d7590 q = 1) : d0 q = 1 := by
    exact ha
  have h29 (q : Pattern) (ha : d7651 q = 1) (hb : d77845 q = 1) : d79941 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7651, d77845, d79941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16491 q ha hb
    | true =>
      simp only [d7651, d77845, d79941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q hb ha
  have h30 (q : Pattern) (ha : d77845 q = 1) (hb : d85512 q = 1) : d79942 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85512, d79942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q hb ha
    | true =>
      simp only [d85512, d79942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h31 (q : Pattern) (ha : d7656 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7656, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16492 q ha hb
    | true =>
      simp only [d7656, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h32 (q : Pattern) (ha : d7657 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h31 q ha hb
    | true =>
      simp only [d7657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h33 (q : Pattern) (ha : d77845 q = 1) (hb : d85513 q = 1) : d110082 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85513, d110082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
    | true =>
      simp only [d85513, d110082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h32 q hb ha
  have h34 (q : Pattern) (ha : d77845 q = 1) (hb : d85514 q = 1) : d110083 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85514, d110083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
    | true =>
      simp only [d85514, d110083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h33 q ha hb
  have h35 (q : Pattern) (ha : d77845 q = 1) (hb : d85515 q = 1) : d110084 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85515, d110084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d85515, d110084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h34 q ha hb
  have h36 (q : Pattern) (ha : d77845 q = 1) (hb : d85516 q = 1) : d110085 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85516, d110085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d85516, d110085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h35 q ha hb
  exact h36 p ha hb
theorem andIntro16494 (p : Pattern) (ha : d77845 p = 1) (hb : d85523 p = 1) : d110094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7590 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7651 q = 1) (hb : d77845 q = 1) : d79941 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7651, d77845, d79941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16491 q ha hb
    | true =>
      simp only [d7651, d77845, d79941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85512 q = 1) : d79942 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85512, d79942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85512, d79942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7656 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7656, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16492 q ha hb
    | true =>
      simp only [d7656, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7657 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d85513 q = 1) : d110082 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85513, d110082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85513, d110082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85521 q = 1) : d110092 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85521, d110092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85521, d110092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85522 q = 1) : d110093 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85522, d110093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85522, d110093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85523 q = 1) : d110094 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85523, d110094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85523, d110094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16495 (p : Pattern) (ha : d7687 p = 1) (hb : d77844 p = 1) : d79963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7679 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7683 q = 1) (hb : d77842 q = 1) : d7683 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7684 q = 1) (hb : d77844 q = 1) : d79960 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7684, d77844, d79960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7684, d77844, d79960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7685 q = 1) (hb : d77844 q = 1) : d79961 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7685, d79961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7685, d79961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7686 q = 1) (hb : d77844 q = 1) : d79962 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7686, d79962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7686, d79962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7687 q = 1) (hb : d77844 q = 1) : d79963 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7687, d79963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7687, d79963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16496 (p : Pattern) (ha : d7706 p = 1) (hb : d77844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d7683 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d77842 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7703 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d7703, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d7703, d77844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d7704 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d7704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d7705 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d7705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d7705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h6 (q : Pattern) (ha : d7706 q = 1) (hb : d77844 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d7706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  exact h6 p ha hb
theorem andIntro16497 (p : Pattern) (ha : d77845 p = 1) (hb : d85533 p = 1) : d110103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d7691 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d7692 q = 1) (hb : d77845 q = 1) : d79964 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7692, d77845, d79964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16495 q ha hb
    | true =>
      simp only [d7692, d77845, d79964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85529 q = 1) : d79965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d85529, d79965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d85529, d79965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d7707 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d7707, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16496 q ha hb
    | true =>
      simp only [d7707, d77845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d7708 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d7708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d7708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d77845 q = 1) (hb : d85530 q = 1) : d110100 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d85530, d110100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d85530, d110100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85531 q = 1) : d110101 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d85531, d110101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85531, d110101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85532 q = 1) : d110102 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d85532, d110102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85532, d110102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85533 q = 1) : d110103 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d85533, d110103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85533, d110103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro16498 (p : Pattern) (ha : d77845 p = 1) (hb : d85539 p = 1) : d110109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d7588 q = 1) (hb : d77845 q = 1) : d79896 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7588, d79896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d7588, d79896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16480 q ha hb
  have h2 (q : Pattern) (ha : d7589 q = 1) (hb : d77845 q = 1) : d79897 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7589, d79897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d7589, d79897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d7597 q = 1) (hb : d77845 q = 1) : d79905 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7597, d79905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16480 q ha hb
    | true =>
      simp only [d7597, d79905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16482 q ha hb
  have h4 (q : Pattern) (ha : d7598 q = 1) (hb : d77845 q = 1) : d79906 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d7598, d79906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d7598, d79906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d7599 q = 1) (hb : d77845 q = 1) : d79907 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d7599, d79907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d7599, d79907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85517 q = 1) : d110086 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85517, d110086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16488 q ha hb
    | true =>
      simp only [d85517, d110086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16493 q ha hb
  have h7 (q : Pattern) (ha : d7664 q = 1) (hb : d77845 q = 1) : d110088 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d7664, d110088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16483 q ha hb
    | true =>
      simp only [d7664, d110088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8207 q ha hb
  have h8 (q : Pattern) (ha : d77845 q = 1) (hb : d85518 q = 1) : d110089 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85518, d110089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d85518, d110089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d77845 q = 1) (hb : d85519 q = 1) : d110090 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85519, d110090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d85519, d110090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d77845 q = 1) (hb : d85520 q = 1) : d110091 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85520, d110091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d85520, d110091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d77845 q = 1) (hb : d85524 q = 1) : d110095 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85524, d110095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85524, d110095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16494 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8208 q ha hb
  have h13 (q : Pattern) (ha : d77845 q = 1) (hb : d85525 q = 1) : d110096 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85525, d110096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d85525, d110096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d77845 q = 1) (hb : d85526 q = 1) : d110097 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85526, d110097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d85526, d110097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d77845 q = 1) (hb : d85527 q = 1) : d110098 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85527, d110098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d85527, d110098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d77845 q = 1) (hb : d85528 q = 1) : d110099 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85528, d110099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d85528, d110099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d77845 q = 1) (hb : d85534 q = 1) : d110104 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d85534, d110104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85534, d110104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16497 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro8210 q ha hb
  have h19 (q : Pattern) (ha : d77845 q = 1) (hb : d85535 q = 1) : d110105 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d85535, d110105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d85535, d110105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d77845 q = 1) (hb : d85536 q = 1) : d110106 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d85536, d110106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d85536, d110106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d77845 q = 1) (hb : d85537 q = 1) : d110107 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d85537, d110107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d85537, d110107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d77845 q = 1) (hb : d85538 q = 1) : d110108 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d85538, d110108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d85538, d110108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d77845 q = 1) (hb : d85539 q = 1) : d110109 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d85539, d110109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d85539, d110109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro16499 (p : Pattern) (ha : d77845 p = 1) (hb : d85545 p = 1) : d110115 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d77845 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d77845 q = 1) (hb : d85540 q = 1) : d110110 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d85540, d110110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85540, d110110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16498 q ha hb
  have h2 (q : Pattern) (ha : d77845 q = 1) (hb : d85541 q = 1) : d110111 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d85541, d110111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85541, d110111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d77845 q = 1) (hb : d85542 q = 1) : d110112 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d85542, d110112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85542, d110112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d77845 q = 1) (hb : d85543 q = 1) : d110113 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d85543, d110113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85543, d110113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d77845 q = 1) (hb : d85544 q = 1) : d110114 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d85544, d110114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85544, d110114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d77845 q = 1) (hb : d85545 q = 1) : d110115 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d85545, d110115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d85545, d110115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
