import NetHack.Soko22Hazard87.AndIntroBlocks0168
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro42250 (p : Pattern) (ha : d130785 p = 1) (hb : d187788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130759 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130771 q = 1) (hb : d187783 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130771, d187783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42249 q ha hb
    | true =>
      simp only [d130771, d187783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42176 q hb ha
  have h3 (q : Pattern) (ha : d130772 q = 1) (hb : d187784 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130772, d187784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130772, d187784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130781 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130782 q = 1) (hb : d187785 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130782, d187785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130782, d187785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130783 q = 1) (hb : d187786 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130783, d187786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130783, d187786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130784 q = 1) (hb : d187787 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130784, d187787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130784, d187787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130785 q = 1) (hb : d187788 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130785, d187788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130785, d187788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42251 (p : Pattern) (ha : d130798 p = 1) (hb : d187794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130786 q = 1) (hb : d187789 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130786, d187789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130786, d187789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42250 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130793 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130794 q = 1) (hb : d187790 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130794, d187790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130794, d187790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130795 q = 1) (hb : d187791 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130795, d187791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130795, d187791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130796 q = 1) (hb : d187792 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130796, d187792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130796, d187792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130797 q = 1) (hb : d187793 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130797, d187793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130797, d187793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130798 q = 1) (hb : d187794 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130798, d187794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130798, d187794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42252 (p : Pattern) (ha : d130804 p = 1) (hb : d187800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130799 q = 1) (hb : d187795 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130799, d187795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130799, d187795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42251 q ha hb
  have h2 (q : Pattern) (ha : d130800 q = 1) (hb : d187796 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130800, d187796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130800, d187796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130801 q = 1) (hb : d187797 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130801, d187797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130801, d187797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130802 q = 1) (hb : d187798 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130802, d187798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130802, d187798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130803 q = 1) (hb : d187799 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130803, d187799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130803, d187799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130804 q = 1) (hb : d187800 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130804, d187800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130804, d187800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42253 (p : Pattern) (ha : d130827 p = 1) (hb : d187806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19503 q = 1) (hb : d128059 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19503, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42209 q ha hb
    | true =>
      simp only [d19503, d128059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42199 q ha hb
  have h2 (q : Pattern) (ha : d19504 q = 1) (hb : d128060 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19504, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19504, d128060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19505 q = 1) (hb : d128061 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19505, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19505, d128061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19515 q = 1) (hb : d128062 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19515, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42199 q ha hb
    | true =>
      simp only [d19515, d128062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42211 q ha hb
  have h5 (q : Pattern) (ha : d19516 q = 1) (hb : d128063 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19516, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19516, d128063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19517 q = 1) (hb : d128064 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19517, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19517, d128064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19518 q = 1) (hb : d128065 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19518, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19518, d128065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19550 q = 1) (hb : d128079 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19550, d128079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42199 q ha hb
    | true =>
      simp only [d19550, d128079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42200 q ha hb
  have h9 (q : Pattern) (ha : d19551 q = 1) (hb : d128080 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19551, d128080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19551, d128080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19552 q = 1) (hb : d128081 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19552, d128081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19552, d128081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19553 q = 1) (hb : d128082 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19553, d128082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19553, d128082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d128092 q = 1) (hb : d187805 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d128092, d187805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d128092, d187805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d17162 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42205 q ha hb
    | true =>
      simp only [d17162, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
  have h14 (q : Pattern) (ha : d19525 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19525, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19525, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d19526 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19526, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19526, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d17165 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
    | true =>
      simp only [d17165, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42204 q ha hb
  have h17 (q : Pattern) (ha : d19527 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19527, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d19527, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d19528 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19528, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19528, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d19529 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19529, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19529, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d17169 q = 1) (hb : d101762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17169, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
    | true =>
      simp only [d17169, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42197 q ha hb
  have h21 (q : Pattern) (ha : d19555 q = 1) (hb : d101763 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19555, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19555, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d19556 q = 1) (hb : d101764 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19556, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19556, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d19557 q = 1) (hb : d101765 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19557, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d19557, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d101775 q = 1) (hb : d132514 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d101775, d132514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d101775, d132514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
  have h25 (q : Pattern) (ha : d130827 q = 1) (hb : d187806 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130827, d187806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d130827, d187806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  exact h25 p ha hb
theorem andIntro42254 (p : Pattern) (ha : d130833 p = 1) (hb : d187812 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130828 q = 1) (hb : d187807 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130828, d187807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42253 q ha hb
    | true =>
      simp only [d130828, d187807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130829 q = 1) (hb : d187808 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130829, d187808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130829, d187808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19560 q = 1) (hb : d130820 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19560, d130820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42201 q ha hb
    | true =>
      simp only [d19560, d130820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19561 q = 1) (hb : d130821 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19561, d130821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19561, d130821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130830 q = 1) (hb : d187809 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130830, d187809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130830, d187809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130831 q = 1) (hb : d187810 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130831, d187810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130831, d187810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130832 q = 1) (hb : d187811 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130832, d187811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130832, d187811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130833 q = 1) (hb : d187812 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130833, d187812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130833, d187812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42255 (p : Pattern) (ha : d130852 p = 1) (hb : d187818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d130826 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130838 q = 1) (hb : d187813 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130838, d187813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42254 q ha hb
    | true =>
      simp only [d130838, d187813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42202 q hb ha
  have h3 (q : Pattern) (ha : d130839 q = 1) (hb : d187814 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130839, d187814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130839, d187814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d130848 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130849 q = 1) (hb : d187815 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130849, d187815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130849, d187815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130850 q = 1) (hb : d187816 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130850, d187816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130850, d187816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130851 q = 1) (hb : d187817 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130851, d187817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130851, d187817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130852 q = 1) (hb : d187818 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130852, d187818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130852, d187818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42256 (p : Pattern) (ha : d130865 p = 1) (hb : d187824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130853 q = 1) (hb : d187819 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130853, d187819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130853, d187819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42255 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130860 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130861 q = 1) (hb : d187820 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130861, d187820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130861, d187820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130862 q = 1) (hb : d187821 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130862, d187821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130862, d187821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130863 q = 1) (hb : d187822 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130863, d187822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130863, d187822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130864 q = 1) (hb : d187823 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130864, d187823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130864, d187823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130865 q = 1) (hb : d187824 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130865, d187824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130865, d187824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42257 (p : Pattern) (ha : d130871 p = 1) (hb : d187830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130866 q = 1) (hb : d187825 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130866, d187825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130866, d187825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42256 q ha hb
  have h2 (q : Pattern) (ha : d130867 q = 1) (hb : d187826 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130867, d187826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130867, d187826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130868 q = 1) (hb : d187827 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130868, d187827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130868, d187827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130869 q = 1) (hb : d187828 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130869, d187828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130869, d187828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130870 q = 1) (hb : d187829 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130870, d187829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130870, d187829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130871 q = 1) (hb : d187830 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130871, d187830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130871, d187830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42258 (p : Pattern) (ha : d130877 p = 1) (hb : d187836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d130620 q = 1) (hb : d187725 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130620, d187725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42236 q ha hb
    | true =>
      simp only [d130620, d187725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42239 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130674 q = 1) (hb : d187744 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130674, d187744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130674, d187744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42242 q ha hb
  have h3 (q : Pattern) (ha : d130675 q = 1) (hb : d187745 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130675, d187745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130675, d187745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130739 q = 1) (hb : d187772 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130739, d187772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130739, d187772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42247 q ha hb
  have h5 (q : Pattern) (ha : d130740 q = 1) (hb : d187773 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130740, d187773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130740, d187773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130741 q = 1) (hb : d187774 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130741, d187774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130741, d187774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130805 q = 1) (hb : d187801 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130805, d187801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130805, d187801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42252 q ha hb
  have h8 (q : Pattern) (ha : d130806 q = 1) (hb : d187802 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130806, d187802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130806, d187802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130807 q = 1) (hb : d187803 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130807, d187803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130807, d187803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130808 q = 1) (hb : d187804 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130808, d187804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130808, d187804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d130872 q = 1) (hb : d187831 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130872, d187831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130872, d187831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42257 q ha hb
  have h12 (q : Pattern) (ha : d130873 q = 1) (hb : d187832 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130873, d187832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130873, d187832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d130874 q = 1) (hb : d187833 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130874, d187833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130874, d187833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d130875 q = 1) (hb : d187834 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130875, d187834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130875, d187834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d130876 q = 1) (hb : d187835 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d130876, d187835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d130876, d187835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d130877 q = 1) (hb : d187836 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d130877, d187836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d130877, d187836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro42259 (p : Pattern) (ha : d130883 p = 1) (hb : d187842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130878 q = 1) (hb : d187837 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d130878, d187837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42258 q ha hb
    | true =>
      simp only [d130878, d187837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130879 q = 1) (hb : d187838 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d130879, d187838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130879, d187838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130880 q = 1) (hb : d187839 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d130880, d187839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130880, d187839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130881 q = 1) (hb : d187840 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d130881, d187840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130881, d187840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130882 q = 1) (hb : d187841 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d130882, d187841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130882, d187841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130883 q = 1) (hb : d187842 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d130883, d187842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130883, d187842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42260 (p : Pattern) (ha : d130889 p = 1) (hb : d187848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130884 q = 1) (hb : d187843 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d130884, d187843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42259 q ha hb
    | true =>
      simp only [d130884, d187843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130885 q = 1) (hb : d187844 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d130885, d187844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130885, d187844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130886 q = 1) (hb : d187845 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d130886, d187845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130886, d187845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130887 q = 1) (hb : d187846 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d130887, d187846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130887, d187846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130888 q = 1) (hb : d187847 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d130888, d187847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130888, d187847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130889 q = 1) (hb : d187848 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d130889, d187848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130889, d187848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42261 (p : Pattern) (ha : d130895 p = 1) (hb : d187854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130890 q = 1) (hb : d187849 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d130890, d187849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42260 q ha hb
    | true =>
      simp only [d130890, d187849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130891 q = 1) (hb : d187850 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d130891, d187850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130891, d187850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130892 q = 1) (hb : d187851 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d130892, d187851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130892, d187851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130893 q = 1) (hb : d187852 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d130893, d187852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130893, d187852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130894 q = 1) (hb : d187853 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d130894, d187853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130894, d187853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130895 q = 1) (hb : d187854 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d130895, d187854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130895, d187854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42262 (p : Pattern) (ha : d130901 p = 1) (hb : d187860 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130896 q = 1) (hb : d187855 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d130896, d187855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42261 q ha hb
    | true =>
      simp only [d130896, d187855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130897 q = 1) (hb : d187856 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d130897, d187856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130897, d187856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130898 q = 1) (hb : d187857 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d130898, d187857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130898, d187857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130899 q = 1) (hb : d187858 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d130899, d187858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130899, d187858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130900 q = 1) (hb : d187859 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d130900, d187859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130900, d187859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130901 q = 1) (hb : d187860 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d130901, d187860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130901, d187860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42263 (p : Pattern) (ha : d130907 p = 1) (hb : d187866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130902 q = 1) (hb : d187861 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d130902, d187861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42262 q ha hb
    | true =>
      simp only [d130902, d187861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130903 q = 1) (hb : d187862 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d130903, d187862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130903, d187862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130904 q = 1) (hb : d187863 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d130904, d187863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130904, d187863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130905 q = 1) (hb : d187864 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d130905, d187864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130905, d187864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130906 q = 1) (hb : d187865 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d130906, d187865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130906, d187865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130907 q = 1) (hb : d187866 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d130907, d187866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130907, d187866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42264 (p : Pattern) (ha : d130913 p = 1) (hb : d187872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130908 q = 1) (hb : d187867 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d130908, d187867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42263 q ha hb
    | true =>
      simp only [d130908, d187867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130909 q = 1) (hb : d187868 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d130909, d187868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130909, d187868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130910 q = 1) (hb : d187869 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d130910, d187869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130910, d187869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130911 q = 1) (hb : d187870 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d130911, d187870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130911, d187870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130912 q = 1) (hb : d187871 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d130912, d187871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130912, d187871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130913 q = 1) (hb : d187872 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d130913, d187872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130913, d187872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42265 (p : Pattern) (ha : d130919 p = 1) (hb : d187878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130914 q = 1) (hb : d187873 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d130914, d187873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42264 q ha hb
    | true =>
      simp only [d130914, d187873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130915 q = 1) (hb : d187874 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d130915, d187874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130915, d187874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130916 q = 1) (hb : d187875 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d130916, d187875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130916, d187875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130917 q = 1) (hb : d187876 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d130917, d187876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130917, d187876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130918 q = 1) (hb : d187877 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d130918, d187877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130918, d187877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130919 q = 1) (hb : d187878 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d130919, d187878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130919, d187878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42266 (p : Pattern) (ha : d18695 p = 1) (hb : d130924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20420 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18555 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d18691 q = 1) (hb : d130920 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18691, d130920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18691, d130920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20398 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d18692 q = 1) (hb : d130921 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18692, d130921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18692, d130921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18693 q = 1) (hb : d130922 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18693, d130922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18693, d130922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18694 q = 1) (hb : d130923 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18694, d130923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18694, d130923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18695 q = 1) (hb : d130924 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18695, d130924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18695, d130924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42267 (p : Pattern) (ha : d130930 p = 1) (hb : d187684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18696 q = 1) (hb : d130925 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18696, d130925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18696, d130925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42266 q ha hb
  have h2 (q : Pattern) (ha : d130926 q = 1) (hb : d187680 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130926, d187680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130926, d187680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d130927 q = 1) (hb : d187681 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130927, d187681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130927, d187681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d130928 q = 1) (hb : d187682 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130928, d187682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130928, d187682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130929 q = 1) (hb : d187683 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130929, d187683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130929, d187683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130930 q = 1) (hb : d187684 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130930, d187684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130930, d187684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42268 (p : Pattern) (ha : d130940 p = 1) (hb : d187694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20452 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d18592 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130936 q = 1) (hb : d187690 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130936, d187690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130936, d187690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20467 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130937 q = 1) (hb : d187691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130937, d187691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130937, d187691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130938 q = 1) (hb : d187692 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130938, d187692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130938, d187692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130939 q = 1) (hb : d187693 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130939, d187693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130939, d187693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130940 q = 1) (hb : d187694 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130940, d187694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130940, d187694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42269 (p : Pattern) (ha : d130946 p = 1) (hb : d187700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130941 q = 1) (hb : d187695 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130941, d187695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130941, d187695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42268 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20478 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130942 q = 1) (hb : d187696 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130942, d187696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130942, d187696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130943 q = 1) (hb : d187697 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130943, d187697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130943, d187697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130944 q = 1) (hb : d187698 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130944, d187698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130944, d187698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130945 q = 1) (hb : d187699 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130945, d187699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130945, d187699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130946 q = 1) (hb : d187700 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130946, d187700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130946, d187700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42270 (p : Pattern) (ha : d130952 p = 1) (hb : d187706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d20412 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130931 q = 1) (hb : d187685 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130931, d187685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130931, d187685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42267 q ha hb
  have h3 (q : Pattern) (ha : d130932 q = 1) (hb : d187686 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130932, d187686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130932, d187686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130933 q = 1) (hb : d187687 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130933, d187687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130933, d187687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130934 q = 1) (hb : d187688 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130934, d187688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130934, d187688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130935 q = 1) (hb : d187689 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130935, d187689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130935, d187689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130947 q = 1) (hb : d187701 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130947, d187701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130947, d187701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42269 q ha hb
  have h8 (q : Pattern) (ha : d130948 q = 1) (hb : d187702 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130948, d187702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130948, d187702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130949 q = 1) (hb : d187703 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130949, d187703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130949, d187703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130950 q = 1) (hb : d187704 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130950, d187704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130950, d187704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d130951 q = 1) (hb : d187705 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130951, d187705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130951, d187705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d130952 q = 1) (hb : d187706 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130952, d187706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130952, d187706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro42271 (p : Pattern) (ha : d130957 p = 1) (hb : d187712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20507 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d187707 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130953 q = 1) (hb : d187708 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130953, d187708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130953, d187708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20529 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130954 q = 1) (hb : d187709 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130954, d187709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130954, d187709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130955 q = 1) (hb : d187710 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130955, d187710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130955, d187710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130956 q = 1) (hb : d187711 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130956, d187711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130956, d187711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130957 q = 1) (hb : d187712 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130957, d187712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130957, d187712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42272 (p : Pattern) (ha : d130963 p = 1) (hb : d187718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130958 q = 1) (hb : d187713 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130958, d187713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130958, d187713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42271 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20545 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130959 q = 1) (hb : d187714 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130959, d187714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130959, d187714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130960 q = 1) (hb : d187715 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130960, d187715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130960, d187715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130961 q = 1) (hb : d187716 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130961, d187716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130961, d187716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130962 q = 1) (hb : d187717 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130962, d187717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130962, d187717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130963 q = 1) (hb : d187718 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130963, d187718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130963, d187718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42273 (p : Pattern) (ha : d130969 p = 1) (hb : d187724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130964 q = 1) (hb : d187719 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130964, d187719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130964, d187719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42272 q ha hb
  have h2 (q : Pattern) (ha : d130965 q = 1) (hb : d187720 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130965, d187720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130965, d187720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130966 q = 1) (hb : d187721 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130966, d187721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130966, d187721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130967 q = 1) (hb : d187722 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130967, d187722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130967, d187722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130968 q = 1) (hb : d187723 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130968, d187723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130968, d187723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130969 q = 1) (hb : d187724 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130969, d187724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130969, d187724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42274 (p : Pattern) (ha : d130975 p = 1) (hb : d187731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20575 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d187726 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130971 q = 1) (hb : d187727 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130971, d187727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130971, d187727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20597 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130972 q = 1) (hb : d187728 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130972, d187728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130972, d187728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130973 q = 1) (hb : d187729 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130973, d187729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130973, d187729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130974 q = 1) (hb : d187730 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130974, d187730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130974, d187730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130975 q = 1) (hb : d187731 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130975, d187731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130975, d187731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42275 (p : Pattern) (ha : d130981 p = 1) (hb : d187737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130976 q = 1) (hb : d187732 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130976, d187732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130976, d187732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42274 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20613 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130977 q = 1) (hb : d187733 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130977, d187733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130977, d187733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130978 q = 1) (hb : d187734 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130978, d187734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130978, d187734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130979 q = 1) (hb : d187735 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130979, d187735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130979, d187735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130980 q = 1) (hb : d187736 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130980, d187736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130980, d187736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d130981 q = 1) (hb : d187737 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130981, d187737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130981, d187737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42276 (p : Pattern) (ha : d130987 p = 1) (hb : d187743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130982 q = 1) (hb : d187738 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130982, d187738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130982, d187738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42275 q ha hb
  have h2 (q : Pattern) (ha : d130983 q = 1) (hb : d187739 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130983, d187739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130983, d187739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130984 q = 1) (hb : d187740 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130984, d187740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130984, d187740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130985 q = 1) (hb : d187741 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130985, d187741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130985, d187741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130986 q = 1) (hb : d187742 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130986, d187742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130986, d187742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130987 q = 1) (hb : d187743 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130987, d187743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130987, d187743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42277 (p : Pattern) (ha : d130994 p = 1) (hb : d187759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20644 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d187754 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130990 q = 1) (hb : d187755 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130990, d187755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130990, d187755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20669 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d130991 q = 1) (hb : d187756 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130991, d187756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130991, d187756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d130992 q = 1) (hb : d187757 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130992, d187757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130992, d187757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130993 q = 1) (hb : d187758 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130993, d187758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130993, d187758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130994 q = 1) (hb : d187759 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130994, d187759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130994, d187759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42278 (p : Pattern) (ha : d131000 p = 1) (hb : d187765 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130995 q = 1) (hb : d187760 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130995, d187760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130995, d187760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42277 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20685 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130996 q = 1) (hb : d187761 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130996, d187761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130996, d187761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130997 q = 1) (hb : d187762 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130997, d187762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130997, d187762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d130998 q = 1) (hb : d187763 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130998, d187763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130998, d187763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d130999 q = 1) (hb : d187764 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130999, d187764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130999, d187764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d131000 q = 1) (hb : d187765 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131000, d187765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131000, d187765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42279 (p : Pattern) (ha : d131006 p = 1) (hb : d187771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131001 q = 1) (hb : d187766 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131001, d187766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131001, d187766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42278 q ha hb
  have h2 (q : Pattern) (ha : d131002 q = 1) (hb : d187767 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131002, d187767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131002, d187767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131003 q = 1) (hb : d187768 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131003, d187768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131003, d187768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131004 q = 1) (hb : d187769 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131004, d187769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131004, d187769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131005 q = 1) (hb : d187770 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131005, d187770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131005, d187770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131006 q = 1) (hb : d187771 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131006, d187771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131006, d187771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42280 (p : Pattern) (ha : d131014 p = 1) (hb : d187788 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20717 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d187783 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131010 q = 1) (hb : d187784 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131010, d187784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131010, d187784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20742 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131011 q = 1) (hb : d187785 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131011, d187785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131011, d187785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131012 q = 1) (hb : d187786 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131012, d187786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131012, d187786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131013 q = 1) (hb : d187787 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131013, d187787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131013, d187787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131014 q = 1) (hb : d187788 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131014, d187788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131014, d187788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42281 (p : Pattern) (ha : d131020 p = 1) (hb : d187794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131015 q = 1) (hb : d187789 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131015, d187789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131015, d187789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42280 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20758 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131016 q = 1) (hb : d187790 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131016, d187790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131016, d187790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131017 q = 1) (hb : d187791 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131017, d187791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131017, d187791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131018 q = 1) (hb : d187792 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131018, d187792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131018, d187792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131019 q = 1) (hb : d187793 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131019, d187793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131019, d187793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d131020 q = 1) (hb : d187794 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131020, d187794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131020, d187794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42282 (p : Pattern) (ha : d131026 p = 1) (hb : d187800 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131021 q = 1) (hb : d187795 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131021, d187795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131021, d187795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42281 q ha hb
  have h2 (q : Pattern) (ha : d131022 q = 1) (hb : d187796 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131022, d187796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131022, d187796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131023 q = 1) (hb : d187797 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131023, d187797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131023, d187797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131024 q = 1) (hb : d187798 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131024, d187798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131024, d187798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131025 q = 1) (hb : d187799 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131025, d187799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131025, d187799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131026 q = 1) (hb : d187800 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131026, d187800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131026, d187800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42283 (p : Pattern) (ha : d131035 p = 1) (hb : d187818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d20791 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d187813 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131031 q = 1) (hb : d187814 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d131031, d187814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d131031, d187814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d20816 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d131032 q = 1) (hb : d187815 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d131032, d187815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131032, d187815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131033 q = 1) (hb : d187816 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d131033, d187816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131033, d187816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131034 q = 1) (hb : d187817 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d131034, d187817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131034, d187817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131035 q = 1) (hb : d187818 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d131035, d187818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131035, d187818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42284 (p : Pattern) (ha : d131041 p = 1) (hb : d187824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131036 q = 1) (hb : d187819 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d131036, d187819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131036, d187819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42283 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d20832 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d131037 q = 1) (hb : d187820 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d131037, d187820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131037, d187820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131038 q = 1) (hb : d187821 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d131038, d187821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131038, d187821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131039 q = 1) (hb : d187822 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d131039, d187822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131039, d187822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131040 q = 1) (hb : d187823 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d131040, d187823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131040, d187823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d131041 q = 1) (hb : d187824 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d131041, d187824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131041, d187824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42285 (p : Pattern) (ha : d131047 p = 1) (hb : d187830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131042 q = 1) (hb : d187825 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d131042, d187825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131042, d187825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42284 q ha hb
  have h2 (q : Pattern) (ha : d131043 q = 1) (hb : d187826 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d131043, d187826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131043, d187826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131044 q = 1) (hb : d187827 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d131044, d187827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131044, d187827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131045 q = 1) (hb : d187828 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d131045, d187828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131045, d187828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131046 q = 1) (hb : d187829 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d131046, d187829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131046, d187829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131047 q = 1) (hb : d187830 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d131047, d187830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d131047, d187830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42286 (p : Pattern) (ha : d131053 p = 1) (hb : d187836 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d130970 q = 1) (hb : d187725 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130970, d187725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42270 q ha hb
    | true =>
      simp only [d130970, d187725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42273 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d130988 q = 1) (hb : d187744 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130988, d187744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130988, d187744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42276 q ha hb
  have h3 (q : Pattern) (ha : d130989 q = 1) (hb : d187745 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130989, d187745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d130989, d187745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131007 q = 1) (hb : d187772 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131007, d187772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131007, d187772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42279 q ha hb
  have h5 (q : Pattern) (ha : d131008 q = 1) (hb : d187773 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131008, d187773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131008, d187773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131009 q = 1) (hb : d187774 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131009, d187774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131009, d187774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131027 q = 1) (hb : d187801 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131027, d187801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131027, d187801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42282 q ha hb
  have h8 (q : Pattern) (ha : d131028 q = 1) (hb : d187802 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131028, d187802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131028, d187802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131029 q = 1) (hb : d187803 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131029, d187803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131029, d187803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131030 q = 1) (hb : d187804 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131030, d187804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d131030, d187804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131048 q = 1) (hb : d187831 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d131048, d187831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131048, d187831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42285 q ha hb
  have h12 (q : Pattern) (ha : d131049 q = 1) (hb : d187832 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d131049, d187832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131049, d187832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d131050 q = 1) (hb : d187833 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d131050, d187833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131050, d187833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131051 q = 1) (hb : d187834 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d131051, d187834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131051, d187834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d131052 q = 1) (hb : d187835 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d131052, d187835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d131052, d187835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d131053 q = 1) (hb : d187836 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d131053, d187836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d131053, d187836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro42287 (p : Pattern) (ha : d131059 p = 1) (hb : d187842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131054 q = 1) (hb : d187837 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d131054, d187837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42286 q ha hb
    | true =>
      simp only [d131054, d187837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131055 q = 1) (hb : d187838 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d131055, d187838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131055, d187838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131056 q = 1) (hb : d187839 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d131056, d187839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131056, d187839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131057 q = 1) (hb : d187840 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d131057, d187840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131057, d187840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131058 q = 1) (hb : d187841 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d131058, d187841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131058, d187841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131059 q = 1) (hb : d187842 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d131059, d187842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131059, d187842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42288 (p : Pattern) (ha : d131065 p = 1) (hb : d187848 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131060 q = 1) (hb : d187843 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d131060, d187843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42287 q ha hb
    | true =>
      simp only [d131060, d187843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131061 q = 1) (hb : d187844 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d131061, d187844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131061, d187844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131062 q = 1) (hb : d187845 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d131062, d187845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131062, d187845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131063 q = 1) (hb : d187846 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d131063, d187846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131063, d187846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131064 q = 1) (hb : d187847 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d131064, d187847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131064, d187847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131065 q = 1) (hb : d187848 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d131065, d187848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131065, d187848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42289 (p : Pattern) (ha : d131071 p = 1) (hb : d187854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131066 q = 1) (hb : d187849 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d131066, d187849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42288 q ha hb
    | true =>
      simp only [d131066, d187849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131067 q = 1) (hb : d187850 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d131067, d187850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131067, d187850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131068 q = 1) (hb : d187851 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d131068, d187851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131068, d187851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131069 q = 1) (hb : d187852 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d131069, d187852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131069, d187852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131070 q = 1) (hb : d187853 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d131070, d187853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131070, d187853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131071 q = 1) (hb : d187854 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d131071, d187854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131071, d187854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42290 (p : Pattern) (ha : d131077 p = 1) (hb : d187860 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131072 q = 1) (hb : d187855 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d131072, d187855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42289 q ha hb
    | true =>
      simp only [d131072, d187855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131073 q = 1) (hb : d187856 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d131073, d187856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131073, d187856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131074 q = 1) (hb : d187857 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d131074, d187857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131074, d187857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131075 q = 1) (hb : d187858 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d131075, d187858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131075, d187858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131076 q = 1) (hb : d187859 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d131076, d187859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131076, d187859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131077 q = 1) (hb : d187860 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d131077, d187860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131077, d187860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42291 (p : Pattern) (ha : d131083 p = 1) (hb : d187866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131078 q = 1) (hb : d187861 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d131078, d187861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42290 q ha hb
    | true =>
      simp only [d131078, d187861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131079 q = 1) (hb : d187862 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d131079, d187862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131079, d187862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131080 q = 1) (hb : d187863 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d131080, d187863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131080, d187863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131081 q = 1) (hb : d187864 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d131081, d187864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131081, d187864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131082 q = 1) (hb : d187865 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d131082, d187865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131082, d187865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131083 q = 1) (hb : d187866 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d131083, d187866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131083, d187866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42292 (p : Pattern) (ha : d131089 p = 1) (hb : d187872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131084 q = 1) (hb : d187867 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d131084, d187867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42291 q ha hb
    | true =>
      simp only [d131084, d187867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131085 q = 1) (hb : d187868 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d131085, d187868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131085, d187868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131086 q = 1) (hb : d187869 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d131086, d187869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131086, d187869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131087 q = 1) (hb : d187870 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d131087, d187870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131087, d187870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131088 q = 1) (hb : d187871 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d131088, d187871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131088, d187871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131089 q = 1) (hb : d187872 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d131089, d187872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131089, d187872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42293 (p : Pattern) (ha : d131095 p = 1) (hb : d187878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131090 q = 1) (hb : d187873 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d131090, d187873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42292 q ha hb
    | true =>
      simp only [d131090, d187873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d131091 q = 1) (hb : d187874 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d131091, d187874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d131091, d187874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d131092 q = 1) (hb : d187875 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d131092, d187875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d131092, d187875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d131093 q = 1) (hb : d187876 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d131093, d187876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d131093, d187876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131094 q = 1) (hb : d187877 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d131094, d187877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d131094, d187877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d131095 q = 1) (hb : d187878 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d131095, d187878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d131095, d187878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42294 (p : Pattern) (ha : d18538 p = 1) (hb : d131098 p = 1) : d30 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d24 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d66 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18534 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18534, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18534, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d26 q = 1) (hb : d131098 q = 1) : d26 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18535 q = 1) (hb : d131098 q = 1) : d27 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18535, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18535, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18536 q = 1) (hb : d131098 q = 1) : d28 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18536, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18536, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18537 q = 1) (hb : d131098 q = 1) : d29 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18537, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18537, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d18538 q = 1) (hb : d131098 q = 1) : d30 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18538, d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18538, d30, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h10 p ha hb
theorem andIntro42295 (p : Pattern) (ha : d18548 p = 1) (hb : d131098 p = 1) : d187879 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18539 q = 1) (hb : d131098 q = 1) : d31 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18539, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42294 q ha hb
    | true =>
      simp only [d18539, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18540 q = 1) (hb : d131098 q = 1) : d32 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18540, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18540, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18541 q = 1) (hb : d131098 q = 1) : d33 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18541, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18541, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18542 q = 1) (hb : d131098 q = 1) : d34 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18542, d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18542, d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18543 q = 1) (hb : d131098 q = 1) : d35 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18543, d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18543, d35, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18547 q = 1) (hb : d131098 q = 1) : d18547 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18548 q = 1) (hb : d131098 q = 1) : d187879 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18548, d187879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18548, d187879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42296 (p : Pattern) (ha : d18554 p = 1) (hb : d131098 p = 1) : d187885 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18549 q = 1) (hb : d131098 q = 1) : d187880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18549, d187880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42295 q ha hb
    | true =>
      simp only [d18549, d187880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18550 q = 1) (hb : d131098 q = 1) : d187881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18550, d187881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18550, d187881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18551 q = 1) (hb : d131098 q = 1) : d187882 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18551, d187882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18551, d187882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18552 q = 1) (hb : d131098 q = 1) : d187883 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18552, d187883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18552, d187883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18553 q = 1) (hb : d131098 q = 1) : d187884 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18553, d187884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18553, d187884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18554 q = 1) (hb : d131098 q = 1) : d187885 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18554, d187885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18554, d187885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42297 (p : Pattern) (ha : d18560 p = 1) (hb : d131098 p = 1) : d187891 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18555 q = 1) (hb : d131098 q = 1) : d187886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18555, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42296 q ha hb
    | true =>
      simp only [d18555, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18556 q = 1) (hb : d131098 q = 1) : d187887 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18556, d187887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18556, d187887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18557 q = 1) (hb : d131098 q = 1) : d187888 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18557, d187888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18557, d187888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18558 q = 1) (hb : d131098 q = 1) : d187889 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18558, d187889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18558, d187889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18559 q = 1) (hb : d131098 q = 1) : d187890 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18559, d187890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18559, d187890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18560 q = 1) (hb : d131098 q = 1) : d187891 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18560, d187891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18560, d187891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42298 (p : Pattern) (ha : d18566 p = 1) (hb : d131098 p = 1) : d187897 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18561 q = 1) (hb : d131098 q = 1) : d187892 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18561, d187892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18561, d187892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42297 q ha hb
  have h2 (q : Pattern) (ha : d18562 q = 1) (hb : d131098 q = 1) : d187893 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d18562, d187893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18562, d187893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d18563 q = 1) (hb : d131098 q = 1) : d187894 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d18563, d187894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18563, d187894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18564 q = 1) (hb : d131098 q = 1) : d187895 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d18564, d187895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18564, d187895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18565 q = 1) (hb : d131098 q = 1) : d187896 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d18565, d187896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18565, d187896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18566 q = 1) (hb : d131098 q = 1) : d187897 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d18566, d187897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18566, d187897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42299 (p : Pattern) (ha : d18575 p = 1) (hb : d131098 p = 1) : d144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d138 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d226 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18571 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18571, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18571, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d140 q = 1) (hb : d131098 q = 1) : d140 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18572 q = 1) (hb : d131098 q = 1) : d141 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18572, d141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18572, d141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18573 q = 1) (hb : d131098 q = 1) : d142 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18573, d142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18573, d142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d24 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d66 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d18534 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18534, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18534, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d26 q = 1) (hb : d131098 q = 1) : d26 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d18535 q = 1) (hb : d131098 q = 1) : d27 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18535, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18535, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18536 q = 1) (hb : d131098 q = 1) : d28 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18536, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18536, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d18574 q = 1) (hb : d131098 q = 1) : d143 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18574, d143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18574, d143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18537 q = 1) (hb : d131098 q = 1) : d29 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18537, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d18537, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h17 (q : Pattern) (ha : d18575 q = 1) (hb : d131098 q = 1) : d144 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18575, d144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18575, d144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro42300 (p : Pattern) (ha : d18585 p = 1) (hb : d131098 p = 1) : d187902 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18576 q = 1) (hb : d131098 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18576, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42299 q ha hb
    | true =>
      simp only [d18576, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42294 q ha hb
  have h2 (q : Pattern) (ha : d18577 q = 1) (hb : d131098 q = 1) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18577, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18578 q = 1) (hb : d131098 q = 1) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18578, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18539 q = 1) (hb : d131098 q = 1) : d31 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18539, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42294 q ha hb
    | true =>
      simp only [d18539, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18540 q = 1) (hb : d131098 q = 1) : d32 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18540, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18540, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18541 q = 1) (hb : d131098 q = 1) : d33 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18541, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18541, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18579 q = 1) (hb : d131098 q = 1) : d148 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18579, d148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18579, d148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18542 q = 1) (hb : d131098 q = 1) : d34 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18542, d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18542, d34, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18580 q = 1) (hb : d131098 q = 1) : d149 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18580, d149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18580, d149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18584 q = 1) (hb : d131098 q = 1) : d18584 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d18585 q = 1) (hb : d131098 q = 1) : d187902 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18585, d187902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18585, d187902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42301 (p : Pattern) (ha : d18591 p = 1) (hb : d131098 p = 1) : d187908 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18586 q = 1) (hb : d131098 q = 1) : d187903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18586, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42300 q ha hb
    | true =>
      simp only [d18586, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18587 q = 1) (hb : d131098 q = 1) : d187904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18587, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18587, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18549 q = 1) (hb : d131098 q = 1) : d187880 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18549, d187880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42295 q ha hb
    | true =>
      simp only [d18549, d187880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18550 q = 1) (hb : d131098 q = 1) : d187881 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18550, d187881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18550, d187881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18588 q = 1) (hb : d131098 q = 1) : d187905 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18588, d187905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18588, d187905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18589 q = 1) (hb : d131098 q = 1) : d187906 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18589, d187906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18589, d187906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18590 q = 1) (hb : d131098 q = 1) : d187907 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18590, d187907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18590, d187907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18591 q = 1) (hb : d131098 q = 1) : d187908 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18591, d187908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18591, d187908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42302 (p : Pattern) (ha : d131098 p = 1) (hb : d132592 p = 1) : d187914 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18592 q = 1) (hb : d131098 q = 1) : d187909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18592, d187909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42301 q ha hb
    | true =>
      simp only [d18592, d187909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42296 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132588 q = 1) : d187910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132588, d187910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132588, d187910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d18555 q = 1) (hb : d131098 q = 1) : d187886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18555, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42296 q ha hb
    | true =>
      simp only [d18555, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18556 q = 1) (hb : d131098 q = 1) : d187887 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18556, d187887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18556, d187887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132589 q = 1) : d187911 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132589, d187911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132589, d187911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132590 q = 1) : d187912 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132590, d187912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132590, d187912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131098 q = 1) (hb : d132591 q = 1) : d187913 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132591, d187913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132591, d187913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131098 q = 1) (hb : d132592 q = 1) : d187914 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132592, d187914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132592, d187914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42303 (p : Pattern) (ha : d131098 p = 1) (hb : d132598 p = 1) : d187920 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d132593 q = 1) : d187915 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132593, d187915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132593, d187915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42302 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132594 q = 1) : d187916 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132594, d187916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132594, d187916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d132595 q = 1) : d187917 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132595, d187917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132595, d187917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d132596 q = 1) : d187918 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132596, d187918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132596, d187918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132597 q = 1) : d187919 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132597, d187919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132597, d187919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132598 q = 1) : d187920 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132598, d187920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132598, d187920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42304 (p : Pattern) (ha : d18695 p = 1) (hb : d131098 p = 1) : d187950 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18555 q = 1) (hb : d131098 q = 1) : d187886 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18555, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42296 q ha hb
    | true =>
      simp only [d18555, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18691 q = 1) (hb : d131098 q = 1) : d187946 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18691, d187946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18691, d187946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18692 q = 1) (hb : d131098 q = 1) : d187947 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18692, d187947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18692, d187947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18693 q = 1) (hb : d131098 q = 1) : d187948 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18693, d187948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18693, d187948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18694 q = 1) (hb : d131098 q = 1) : d187949 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18694, d187949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18694, d187949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18695 q = 1) (hb : d131098 q = 1) : d187950 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18695, d187950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18695, d187950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42305 (p : Pattern) (ha : d18639 p = 1) (hb : d131098 p = 1) : d15966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d412 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18631 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18631, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18631, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d320 q = 1) (hb : d131098 q = 1) : d320 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18632 q = 1) (hb : d131098 q = 1) : d321 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18632, d321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18632, d321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18633 q = 1) (hb : d131098 q = 1) : d322 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18633, d322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18633, d322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d138 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d226 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d226, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d226, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d18571 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18571, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18571, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d140 q = 1) (hb : d131098 q = 1) : d140 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d18572 q = 1) (hb : d131098 q = 1) : d141 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18572, d141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18572, d141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18573 q = 1) (hb : d131098 q = 1) : d142 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18573, d142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18573, d142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d18634 q = 1) (hb : d131098 q = 1) : d323 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18634, d323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18634, d323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d9381 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d12599 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d18635 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18635, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18635, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h19 (q : Pattern) (ha : d9384 q = 1) (hb : d131098 q = 1) : d9384 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d18636 q = 1) (hb : d131098 q = 1) : d12493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18636, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d18636, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d18637 q = 1) (hb : d131098 q = 1) : d12494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18637, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d18637, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d24 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d66 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d18534 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18534, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d18534, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d26 q = 1) (hb : d131098 q = 1) : d26 q = 1 := by
    exact ha
  have h26 (q : Pattern) (ha : d18535 q = 1) (hb : d131098 q = 1) : d27 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18535, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d18535, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d18536 q = 1) (hb : d131098 q = 1) : d28 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18536, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d18536, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h28 (q : Pattern) (ha : d18638 q = 1) (hb : d131098 q = 1) : d12495 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18638, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d18638, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d18639 q = 1) (hb : d131098 q = 1) : d15966 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18639, d15966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18639, d15966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro42306 (p : Pattern) (ha : d18649 p = 1) (hb : d131098 p = 1) : d187926 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18640 q = 1) (hb : d131098 q = 1) : d15967 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18640, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42305 q ha hb
    | true =>
      simp only [d18640, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42299 q ha hb
  have h2 (q : Pattern) (ha : d18641 q = 1) (hb : d131098 q = 1) : d15968 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18641, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18641, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18642 q = 1) (hb : d131098 q = 1) : d15969 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18642, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18642, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18576 q = 1) (hb : d131098 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18576, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42299 q ha hb
    | true =>
      simp only [d18576, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42294 q ha hb
  have h5 (q : Pattern) (ha : d18577 q = 1) (hb : d131098 q = 1) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18577, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18578 q = 1) (hb : d131098 q = 1) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18578, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18643 q = 1) (hb : d131098 q = 1) : d15970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18643, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18643, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18539 q = 1) (hb : d131098 q = 1) : d31 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18539, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42294 q ha hb
    | true =>
      simp only [d18539, d31, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18540 q = 1) (hb : d131098 q = 1) : d32 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18540, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18540, d32, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18541 q = 1) (hb : d131098 q = 1) : d33 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18541, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18541, d33, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18579 q = 1) (hb : d131098 q = 1) : d148 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18579, d148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18579, d148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18644 q = 1) (hb : d131098 q = 1) : d15971 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18644, d15971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18644, d15971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18648 q = 1) (hb : d131098 q = 1) : d18648 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d18649 q = 1) (hb : d131098 q = 1) : d187926 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18649, d187926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d18649, d187926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro42307 (p : Pattern) (ha : d18655 p = 1) (hb : d131098 p = 1) : d187932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18650 q = 1) (hb : d131098 q = 1) : d187927 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18650, d187927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42306 q ha hb
    | true =>
      simp only [d18650, d187927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18651 q = 1) (hb : d131098 q = 1) : d187928 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18651, d187928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18651, d187928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18586 q = 1) (hb : d131098 q = 1) : d187903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18586, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42300 q ha hb
    | true =>
      simp only [d18586, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18587 q = 1) (hb : d131098 q = 1) : d187904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18587, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18587, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18652 q = 1) (hb : d131098 q = 1) : d187929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18652, d187929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18652, d187929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18653 q = 1) (hb : d131098 q = 1) : d187930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18653, d187930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18653, d187930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18654 q = 1) (hb : d131098 q = 1) : d187931 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18654, d187931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18654, d187931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18655 q = 1) (hb : d131098 q = 1) : d187932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18655, d187932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18655, d187932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42308 (p : Pattern) (ha : d18683 p = 1) (hb : d131098 p = 1) : d187938 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18586 q = 1) (hb : d131098 q = 1) : d187903 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18586, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42300 q ha hb
    | true =>
      simp only [d18586, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18587 q = 1) (hb : d131098 q = 1) : d187904 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18587, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18587, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18680 q = 1) (hb : d131098 q = 1) : d187935 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18680, d187935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18680, d187935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18681 q = 1) (hb : d131098 q = 1) : d187936 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18681, d187936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18681, d187936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18682 q = 1) (hb : d131098 q = 1) : d187937 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18682, d187937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18682, d187937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18683 q = 1) (hb : d131098 q = 1) : d187938 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18683, d187938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18683, d187938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42309 (p : Pattern) (ha : d131098 p = 1) (hb : d132608 p = 1) : d187944 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18656 q = 1) (hb : d131098 q = 1) : d187933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18656, d187933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42307 q ha hb
    | true =>
      simp only [d18656, d187933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42301 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132604 q = 1) : d187934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132604, d187934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132604, d187934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d18684 q = 1) (hb : d131098 q = 1) : d187939 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18684, d187939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42308 q ha hb
    | true =>
      simp only [d18684, d187939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18685 q = 1) (hb : d131098 q = 1) : d187940 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18685, d187940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18685, d187940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132605 q = 1) : d187941 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132605, d187941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132605, d187941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132606 q = 1) : d187942 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132606, d187942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132606, d187942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131098 q = 1) (hb : d132607 q = 1) : d187943 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132607, d187943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132607, d187943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131098 q = 1) (hb : d132608 q = 1) : d187944 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132608, d187944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132608, d187944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42310 (p : Pattern) (ha : d131098 p = 1) (hb : d132614 p = 1) : d187956 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d132609 q = 1) : d187945 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132609, d187945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132609, d187945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42309 q ha hb
  have h2 (q : Pattern) (ha : d18696 q = 1) (hb : d131098 q = 1) : d187951 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18696, d187951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18696, d187951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42304 q ha hb
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d132610 q = 1) : d187952 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132610, d187952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132610, d187952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d132611 q = 1) : d187953 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132611, d187953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132611, d187953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132612 q = 1) : d187954 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132612, d187954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132612, d187954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132613 q = 1) : d187955 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132613, d187955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132613, d187955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131098 q = 1) (hb : d132614 q = 1) : d187956 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132614, d187956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132614, d187956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42311 (p : Pattern) (ha : d131098 p = 1) (hb : d132620 p = 1) : d187962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18567 q = 1) (hb : d131098 q = 1) : d187898 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d18567, d187898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18567, d187898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42298 q ha hb
  have h2 (q : Pattern) (ha : d18568 q = 1) (hb : d131098 q = 1) : d187899 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d18568, d187899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18568, d187899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18569 q = 1) (hb : d131098 q = 1) : d187900 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d18569, d187900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18569, d187900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18570 q = 1) (hb : d131098 q = 1) : d187901 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d18570, d187901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18570, d187901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132599 q = 1) : d187921 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132599, d187921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132599, d187921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42303 q ha hb
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132600 q = 1) : d187922 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132600, d187922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132600, d187922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131098 q = 1) (hb : d132601 q = 1) : d187923 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132601, d187923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132601, d187923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131098 q = 1) (hb : d132602 q = 1) : d187924 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132602, d187924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132602, d187924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131098 q = 1) (hb : d132603 q = 1) : d187925 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132603, d187925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d132603, d187925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131098 q = 1) (hb : d132615 q = 1) : d187957 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132615, d187957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132615, d187957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42310 q ha hb
  have h11 (q : Pattern) (ha : d131098 q = 1) (hb : d132616 q = 1) : d187958 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132616, d187958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132616, d187958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d131098 q = 1) (hb : d132617 q = 1) : d187959 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132617, d187959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132617, d187959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d131098 q = 1) (hb : d132618 q = 1) : d187960 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132618, d187960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132618, d187960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131098 q = 1) (hb : d132619 q = 1) : d187961 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132619, d187961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132619, d187961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d131098 q = 1) (hb : d132620 q = 1) : d187962 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132620, d187962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d132620, d187962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro42312 (p : Pattern) (ha : d18751 p = 1) (hb : d131098 p = 1) : d187973 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18576 q = 1) (hb : d131098 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18576, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42299 q ha hb
    | true =>
      simp only [d18576, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42294 q ha hb
  have h2 (q : Pattern) (ha : d18577 q = 1) (hb : d131098 q = 1) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18577, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18578 q = 1) (hb : d131098 q = 1) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18578, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18738 q = 1) (hb : d131098 q = 1) : d475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18738, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18738, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18749 q = 1) (hb : d131098 q = 1) : d480 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18749, d480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18749, d480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18750 q = 1) (hb : d131098 q = 1) : d18750 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18751 q = 1) (hb : d131098 q = 1) : d187973 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18751, d187973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18751, d187973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42313 (p : Pattern) (ha : d18811 p = 1) (hb : d131098 p = 1) : d187996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18752 q = 1) (hb : d131098 q = 1) : d187974 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18752, d187974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42312 q ha hb
    | true =>
      simp only [d18752, d187974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18753 q = 1) (hb : d131098 q = 1) : d187975 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18753, d187975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18753, d187975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18808 q = 1) (hb : d131098 q = 1) : d187993 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18808, d187993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18808, d187993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18809 q = 1) (hb : d131098 q = 1) : d187994 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18809, d187994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18809, d187994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18810 q = 1) (hb : d131098 q = 1) : d187995 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18810, d187995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18810, d187995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18811 q = 1) (hb : d131098 q = 1) : d187996 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18811, d187996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18811, d187996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42314 (p : Pattern) (ha : d18817 p = 1) (hb : d131098 p = 1) : d188002 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18812 q = 1) (hb : d131098 q = 1) : d187997 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18812, d187997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42313 q ha hb
    | true =>
      simp only [d18812, d187997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18813 q = 1) (hb : d131098 q = 1) : d187998 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18813, d187998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18813, d187998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18814 q = 1) (hb : d131098 q = 1) : d187999 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18814, d187999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18814, d187999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18815 q = 1) (hb : d131098 q = 1) : d188000 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18815, d188000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18815, d188000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18816 q = 1) (hb : d131098 q = 1) : d188001 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18816, d188001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18816, d188001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18817 q = 1) (hb : d131098 q = 1) : d188002 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18817, d188002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18817, d188002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42315 (p : Pattern) (ha : d18719 p = 1) (hb : d131098 p = 1) : d16077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d542 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d659 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18708 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18708, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18708, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d544 q = 1) (hb : d131098 q = 1) : d544 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18709 q = 1) (hb : d131098 q = 1) : d545 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18709, d545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18709, d545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18710 q = 1) (hb : d131098 q = 1) : d546 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18710, d546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18710, d546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9457 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16156 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16156, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d18711 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18711, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18711, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d9460 q = 1) (hb : d131098 q = 1) : d9460 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d18712 q = 1) (hb : d131098 q = 1) : d16073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18712, d16073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18712, d16073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18713 q = 1) (hb : d131098 q = 1) : d16074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18713, d16074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18713, d16074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d18714 q = 1) (hb : d131098 q = 1) : d16075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18714, d16075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18714, d16075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d9467 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d12858 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d18715 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18715, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18715, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h19 (q : Pattern) (ha : d9470 q = 1) (hb : d131098 q = 1) : d9470 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d18716 q = 1) (hb : d131098 q = 1) : d12748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18716, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d18716, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d18717 q = 1) (hb : d131098 q = 1) : d12749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18717, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d18717, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d9381 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d12599 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d18635 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18635, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d18635, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d9384 q = 1) (hb : d131098 q = 1) : d9384 q = 1 := by
    exact ha
  have h26 (q : Pattern) (ha : d18636 q = 1) (hb : d131098 q = 1) : d12493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18636, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d18636, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d18637 q = 1) (hb : d131098 q = 1) : d12494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18637, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d18637, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h28 (q : Pattern) (ha : d18718 q = 1) (hb : d131098 q = 1) : d16076 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18718, d16076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d18718, d16076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d18719 q = 1) (hb : d131098 q = 1) : d16077 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18719, d16077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18719, d16077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro42316 (p : Pattern) (ha : d18723 p = 1) (hb : d131098 p = 1) : d16081 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9381 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12599 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12599, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12599, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18635 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18635, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18635, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9384 q = 1) (hb : d131098 q = 1) : d9384 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18636 q = 1) (hb : d131098 q = 1) : d12493 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18636, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18636, d12493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18637 q = 1) (hb : d131098 q = 1) : d12494 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18637, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18637, d12494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d24 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d66 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d66, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d66, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d18534 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18534, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18534, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d26 q = 1) (hb : d131098 q = 1) : d26 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d18535 q = 1) (hb : d131098 q = 1) : d27 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18535, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18535, d27, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18536 q = 1) (hb : d131098 q = 1) : d28 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18536, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18536, d28, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d18638 q = 1) (hb : d131098 q = 1) : d12495 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18638, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18638, d12495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18537 q = 1) (hb : d131098 q = 1) : d29 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18537, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d18537, d29, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h17 (q : Pattern) (ha : d18723 q = 1) (hb : d131098 q = 1) : d16081 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18723, d16081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18723, d16081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro42317 (p : Pattern) (ha : d18735 p = 1) (hb : d131098 p = 1) : d187963 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18720 q = 1) (hb : d131098 q = 1) : d16078 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18720, d16078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42315 q ha hb
    | true =>
      simp only [d18720, d16078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42305 q ha hb
  have h2 (q : Pattern) (ha : d18721 q = 1) (hb : d131098 q = 1) : d16079 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18721, d16079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18721, d16079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18722 q = 1) (hb : d131098 q = 1) : d16080 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18722, d16080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18722, d16080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18724 q = 1) (hb : d131098 q = 1) : d16082 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18724, d16082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42305 q ha hb
    | true =>
      simp only [d18724, d16082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42316 q ha hb
  have h5 (q : Pattern) (ha : d18725 q = 1) (hb : d131098 q = 1) : d16083 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18725, d16083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18725, d16083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18726 q = 1) (hb : d131098 q = 1) : d16084 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18726, d16084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18726, d16084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18727 q = 1) (hb : d131098 q = 1) : d16085 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18727, d16085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18727, d16085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18640 q = 1) (hb : d131098 q = 1) : d15967 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18640, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42305 q ha hb
    | true =>
      simp only [d18640, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42299 q ha hb
  have h9 (q : Pattern) (ha : d18641 q = 1) (hb : d131098 q = 1) : d15968 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18641, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18641, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18642 q = 1) (hb : d131098 q = 1) : d15969 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18642, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18642, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18576 q = 1) (hb : d131098 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18576, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42299 q ha hb
    | true =>
      simp only [d18576, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42294 q ha hb
  have h12 (q : Pattern) (ha : d18577 q = 1) (hb : d131098 q = 1) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18577, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18578 q = 1) (hb : d131098 q = 1) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18578, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18643 q = 1) (hb : d131098 q = 1) : d15970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18643, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18643, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18728 q = 1) (hb : d131098 q = 1) : d16086 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18728, d16086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18728, d16086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18734 q = 1) (hb : d131098 q = 1) : d18734 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d18735 q = 1) (hb : d131098 q = 1) : d187963 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18735, d187963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18735, d187963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro42318 (p : Pattern) (ha : d18742 p = 1) (hb : d131098 p = 1) : d187966 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18640 q = 1) (hb : d131098 q = 1) : d15967 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18640, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42305 q ha hb
    | true =>
      simp only [d18640, d15967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42299 q ha hb
  have h2 (q : Pattern) (ha : d18641 q = 1) (hb : d131098 q = 1) : d15968 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18641, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18641, d15968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18642 q = 1) (hb : d131098 q = 1) : d15969 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18642, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18642, d15969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18576 q = 1) (hb : d131098 q = 1) : d145 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18576, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42299 q ha hb
    | true =>
      simp only [d18576, d145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42294 q ha hb
  have h5 (q : Pattern) (ha : d18577 q = 1) (hb : d131098 q = 1) : d146 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18577, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18577, d146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18578 q = 1) (hb : d131098 q = 1) : d147 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18578, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18578, d147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18643 q = 1) (hb : d131098 q = 1) : d15970 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18643, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18643, d15970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18738 q = 1) (hb : d131098 q = 1) : d475 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18738, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18738, d475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18739 q = 1) (hb : d131098 q = 1) : d16035 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18739, d16035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18739, d16035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18741 q = 1) (hb : d131098 q = 1) : d18741 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d18742 q = 1) (hb : d131098 q = 1) : d187966 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18742, d187966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18742, d187966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42319 (p : Pattern) (ha : d18748 p = 1) (hb : d131098 p = 1) : d187972 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18736 q = 1) (hb : d131098 q = 1) : d187964 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18736, d187964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42317 q ha hb
    | true =>
      simp only [d18736, d187964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18737 q = 1) (hb : d131098 q = 1) : d187965 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18737, d187965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18737, d187965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18743 q = 1) (hb : d131098 q = 1) : d187967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18743, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42318 q ha hb
    | true =>
      simp only [d18743, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18744 q = 1) (hb : d131098 q = 1) : d187968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18744, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18744, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18745 q = 1) (hb : d131098 q = 1) : d187969 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18745, d187969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18745, d187969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18746 q = 1) (hb : d131098 q = 1) : d187970 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18746, d187970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18746, d187970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18747 q = 1) (hb : d131098 q = 1) : d187971 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18747, d187971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18747, d187971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18748 q = 1) (hb : d131098 q = 1) : d187972 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18748, d187972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18748, d187972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42320 (p : Pattern) (ha : d18757 p = 1) (hb : d131098 p = 1) : d187979 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18743 q = 1) (hb : d131098 q = 1) : d187967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18743, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42318 q ha hb
    | true =>
      simp only [d18743, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18744 q = 1) (hb : d131098 q = 1) : d187968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18744, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18744, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18752 q = 1) (hb : d131098 q = 1) : d187974 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18752, d187974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42312 q ha hb
    | true =>
      simp only [d18752, d187974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18753 q = 1) (hb : d131098 q = 1) : d187975 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18753, d187975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18753, d187975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18754 q = 1) (hb : d131098 q = 1) : d187976 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18754, d187976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18754, d187976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18755 q = 1) (hb : d131098 q = 1) : d187977 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18755, d187977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18755, d187977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18756 q = 1) (hb : d131098 q = 1) : d187978 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18756, d187978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18756, d187978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18757 q = 1) (hb : d131098 q = 1) : d187979 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18757, d187979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18757, d187979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42321 (p : Pattern) (ha : d18800 p = 1) (hb : d131098 p = 1) : d187985 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18743 q = 1) (hb : d131098 q = 1) : d187967 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18743, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42318 q ha hb
    | true =>
      simp only [d18743, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18744 q = 1) (hb : d131098 q = 1) : d187968 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18744, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18744, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18797 q = 1) (hb : d131098 q = 1) : d187982 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18797, d187982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18797, d187982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18798 q = 1) (hb : d131098 q = 1) : d187983 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18798, d187983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18798, d187983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18799 q = 1) (hb : d131098 q = 1) : d187984 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18799, d187984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18799, d187984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18800 q = 1) (hb : d131098 q = 1) : d187985 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18800, d187985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18800, d187985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42322 (p : Pattern) (ha : d131098 p = 1) (hb : d132625 p = 1) : d187991 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18758 q = 1) (hb : d131098 q = 1) : d187980 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18758, d187980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42319 q ha hb
    | true =>
      simp only [d18758, d187980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42320 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132621 q = 1) : d187981 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132621, d187981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132621, d187981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d18801 q = 1) (hb : d131098 q = 1) : d187986 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18801, d187986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42321 q ha hb
    | true =>
      simp only [d18801, d187986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18802 q = 1) (hb : d131098 q = 1) : d187987 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18802, d187987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18802, d187987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132622 q = 1) : d187988 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132622, d187988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132622, d187988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132623 q = 1) : d187989 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132623, d187989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132623, d187989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131098 q = 1) (hb : d132624 q = 1) : d187990 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132624, d187990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132624, d187990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131098 q = 1) (hb : d132625 q = 1) : d187991 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132625, d187991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132625, d187991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42323 (p : Pattern) (ha : d131098 p = 1) (hb : d132631 p = 1) : d188008 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d132626 q = 1) : d187992 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132626, d187992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132626, d187992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42322 q ha hb
  have h2 (q : Pattern) (ha : d18818 q = 1) (hb : d131098 q = 1) : d188003 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18818, d188003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18818, d188003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42314 q ha hb
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d132627 q = 1) : d188004 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132627, d188004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132627, d188004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d132628 q = 1) : d188005 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132628, d188005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132628, d188005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132629 q = 1) : d188006 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132629, d188006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132629, d188006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132630 q = 1) : d188007 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132630, d188007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132630, d188007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131098 q = 1) (hb : d132631 q = 1) : d188008 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132631, d188008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132631, d188008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42324 (p : Pattern) (ha : d131098 p = 1) (hb : d132637 p = 1) : d188014 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d132632 q = 1) : d188009 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132632, d188009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132632, d188009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42323 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132633 q = 1) : d188010 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132633, d188010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132633, d188010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d132634 q = 1) : d188011 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132634, d188011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132634, d188011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d132635 q = 1) : d188012 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132635, d188012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132635, d188012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132636 q = 1) : d188013 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132636, d188013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132636, d188013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132637 q = 1) : d188014 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132637, d188014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132637, d188014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42325 (p : Pattern) (ha : d18858 p = 1) (hb : d131098 p = 1) : d758 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d318 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d412 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d412, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d412, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18631 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18631, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18631, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d320 q = 1) (hb : d131098 q = 1) : d320 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18632 q = 1) (hb : d131098 q = 1) : d321 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18632, d321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18632, d321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18633 q = 1) (hb : d131098 q = 1) : d322 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18633, d322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18633, d322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d750 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d971 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d18843 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18843, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18843, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d752 q = 1) (hb : d131098 q = 1) : d752 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d18844 q = 1) (hb : d131098 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18844, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18844, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18845 q = 1) (hb : d131098 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18845, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18845, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d18857 q = 1) (hb : d131098 q = 1) : d755 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18857, d755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18857, d755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18851 q = 1) (hb : d131098 q = 1) : d757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18851, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d18851, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h17 (q : Pattern) (ha : d18858 q = 1) (hb : d131098 q = 1) : d758 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18858, d758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18858, d758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro42326 (p : Pattern) (ha : d18862 p = 1) (hb : d131098 p = 1) : d762 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d750 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d971 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18843 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18843, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18843, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d752 q = 1) (hb : d131098 q = 1) : d752 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18844 q = 1) (hb : d131098 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18844, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18844, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18845 q = 1) (hb : d131098 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18845, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18845, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d18851 q = 1) (hb : d131098 q = 1) : d757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18851, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18851, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d18862 q = 1) (hb : d131098 q = 1) : d762 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18862, d762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18862, d762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h10 p ha hb
theorem andIntro42327 (p : Pattern) (ha : d18895 p = 1) (hb : d131098 p = 1) : d188026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18863 q = 1) (hb : d131098 q = 1) : d763 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18863, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42325 q ha hb
    | true =>
      simp only [d18863, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42326 q ha hb
  have h2 (q : Pattern) (ha : d18864 q = 1) (hb : d131098 q = 1) : d764 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18864, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18864, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18865 q = 1) (hb : d131098 q = 1) : d765 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18865, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18865, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18882 q = 1) (hb : d131098 q = 1) : d767 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18882, d767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18882, d767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18893 q = 1) (hb : d131098 q = 1) : d772 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18893, d772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18893, d772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18894 q = 1) (hb : d131098 q = 1) : d18894 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d18895 q = 1) (hb : d131098 q = 1) : d188026 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18895, d188026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18895, d188026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42328 (p : Pattern) (ha : d18970 p = 1) (hb : d131098 p = 1) : d188049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18896 q = 1) (hb : d131098 q = 1) : d188027 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18896, d188027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42327 q ha hb
    | true =>
      simp only [d18896, d188027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18897 q = 1) (hb : d131098 q = 1) : d188028 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18897, d188028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18897, d188028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18967 q = 1) (hb : d131098 q = 1) : d188046 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18967, d188046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18967, d188046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18968 q = 1) (hb : d131098 q = 1) : d188047 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18968, d188047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18968, d188047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18969 q = 1) (hb : d131098 q = 1) : d188048 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18969, d188048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18969, d188048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18970 q = 1) (hb : d131098 q = 1) : d188049 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18970, d188049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18970, d188049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42329 (p : Pattern) (ha : d18976 p = 1) (hb : d131098 p = 1) : d188055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18971 q = 1) (hb : d131098 q = 1) : d188050 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18971, d188050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42328 q ha hb
    | true =>
      simp only [d18971, d188050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18972 q = 1) (hb : d131098 q = 1) : d188051 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18972, d188051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18972, d188051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18973 q = 1) (hb : d131098 q = 1) : d188052 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d18973, d188052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18973, d188052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18974 q = 1) (hb : d131098 q = 1) : d188053 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d18974, d188053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18974, d188053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18975 q = 1) (hb : d131098 q = 1) : d188054 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d18975, d188054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18975, d188054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18976 q = 1) (hb : d131098 q = 1) : d188055 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d18976, d188055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18976, d188055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42330 (p : Pattern) (ha : d18842 p = 1) (hb : d131098 p = 1) : d16274 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d833 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d965 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d965, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d965, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18831 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18831, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18831, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d835 q = 1) (hb : d131098 q = 1) : d835 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18832 q = 1) (hb : d131098 q = 1) : d836 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18832, d836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18832, d836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18833 q = 1) (hb : d131098 q = 1) : d837 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18833, d837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18833, d837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9586 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16356 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16356, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16356, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d18834 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18834, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18834, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d9589 q = 1) (hb : d131098 q = 1) : d9589 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d18835 q = 1) (hb : d131098 q = 1) : d16270 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18835, d16270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18835, d16270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18836 q = 1) (hb : d131098 q = 1) : d16271 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18836, d16271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18836, d16271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d18837 q = 1) (hb : d131098 q = 1) : d16272 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18837, d16272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18837, d16272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d9596 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d14644 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14644, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14644, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d18838 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18838, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18838, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h19 (q : Pattern) (ha : d9599 q = 1) (hb : d131098 q = 1) : d9599 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d18839 q = 1) (hb : d131098 q = 1) : d14529 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18839, d14529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d18839, d14529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d18840 q = 1) (hb : d131098 q = 1) : d14530 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18840, d14530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d18840, d14530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d9467 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d12858 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d18715 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18715, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d18715, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d9470 q = 1) (hb : d131098 q = 1) : d9470 q = 1 := by
    exact ha
  have h26 (q : Pattern) (ha : d18716 q = 1) (hb : d131098 q = 1) : d12748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18716, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d18716, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d18717 q = 1) (hb : d131098 q = 1) : d12749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18717, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d18717, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h28 (q : Pattern) (ha : d18841 q = 1) (hb : d131098 q = 1) : d16273 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18841, d16273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d18841, d16273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d18842 q = 1) (hb : d131098 q = 1) : d16274 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18842, d16274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18842, d16274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro42331 (p : Pattern) (ha : d18847 p = 1) (hb : d131098 p = 1) : d16227 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d542 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d659 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d659, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d659, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18708 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18708, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18708, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d544 q = 1) (hb : d131098 q = 1) : d544 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18709 q = 1) (hb : d131098 q = 1) : d545 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18709, d545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18709, d545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18710 q = 1) (hb : d131098 q = 1) : d546 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18710, d546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18710, d546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9457 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16156 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16156, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16156, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d18711 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18711, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18711, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d9460 q = 1) (hb : d131098 q = 1) : d9460 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d18712 q = 1) (hb : d131098 q = 1) : d16073 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18712, d16073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18712, d16073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18713 q = 1) (hb : d131098 q = 1) : d16074 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18713, d16074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18713, d16074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d18714 q = 1) (hb : d131098 q = 1) : d16075 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18714, d16075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18714, d16075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d9467 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d12858 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d18715 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18715, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18715, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h19 (q : Pattern) (ha : d9470 q = 1) (hb : d131098 q = 1) : d9470 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d18716 q = 1) (hb : d131098 q = 1) : d12748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18716, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d18716, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d18717 q = 1) (hb : d131098 q = 1) : d12749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18717, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d18717, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d750 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d971 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d18843 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18843, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d18843, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d752 q = 1) (hb : d131098 q = 1) : d752 q = 1 := by
    exact ha
  have h26 (q : Pattern) (ha : d18844 q = 1) (hb : d131098 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18844, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d18844, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d18845 q = 1) (hb : d131098 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18845, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d18845, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h28 (q : Pattern) (ha : d18846 q = 1) (hb : d131098 q = 1) : d12750 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18846, d12750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d18846, d12750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d18847 q = 1) (hb : d131098 q = 1) : d16227 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18847, d16227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18847, d16227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro42332 (p : Pattern) (ha : d18852 p = 1) (hb : d131098 p = 1) : d16278 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9467 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d12858 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d12858, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12858, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18715 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18715, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18715, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9470 q = 1) (hb : d131098 q = 1) : d9470 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18716 q = 1) (hb : d131098 q = 1) : d12748 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18716, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18716, d12748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18717 q = 1) (hb : d131098 q = 1) : d12749 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18717, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18717, d12749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d750 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d971 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d971, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d971, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d18843 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18843, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18843, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d752 q = 1) (hb : d131098 q = 1) : d752 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d18844 q = 1) (hb : d131098 q = 1) : d753 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18844, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18844, d753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18845 q = 1) (hb : d131098 q = 1) : d754 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18845, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18845, d754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d18846 q = 1) (hb : d131098 q = 1) : d12750 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18846, d12750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18846, d12750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18851 q = 1) (hb : d131098 q = 1) : d757 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18851, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d18851, d757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h17 (q : Pattern) (ha : d18852 q = 1) (hb : d131098 q = 1) : d16278 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d18852, d16278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18852, d16278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro42333 (p : Pattern) (ha : d18879 p = 1) (hb : d131098 p = 1) : d188016 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18848 q = 1) (hb : d131098 q = 1) : d16275 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18848, d16275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42330 q ha hb
    | true =>
      simp only [d18848, d16275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42331 q ha hb
  have h2 (q : Pattern) (ha : d18849 q = 1) (hb : d131098 q = 1) : d16276 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18849, d16276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18849, d16276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18850 q = 1) (hb : d131098 q = 1) : d16277 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18850, d16277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18850, d16277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18853 q = 1) (hb : d131098 q = 1) : d16279 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18853, d16279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42331 q ha hb
    | true =>
      simp only [d18853, d16279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42332 q ha hb
  have h5 (q : Pattern) (ha : d18854 q = 1) (hb : d131098 q = 1) : d16280 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18854, d16280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18854, d16280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18855 q = 1) (hb : d131098 q = 1) : d16281 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18855, d16281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18855, d16281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18856 q = 1) (hb : d131098 q = 1) : d16282 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18856, d16282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18856, d16282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18859 q = 1) (hb : d131098 q = 1) : d16228 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18859, d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42331 q ha hb
    | true =>
      simp only [d18859, d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42325 q ha hb
  have h9 (q : Pattern) (ha : d18860 q = 1) (hb : d131098 q = 1) : d16229 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18860, d16229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18860, d16229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18861 q = 1) (hb : d131098 q = 1) : d16230 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18861, d16230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18861, d16230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d18863 q = 1) (hb : d131098 q = 1) : d763 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18863, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42325 q ha hb
    | true =>
      simp only [d18863, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42326 q ha hb
  have h12 (q : Pattern) (ha : d18864 q = 1) (hb : d131098 q = 1) : d764 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18864, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18864, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18865 q = 1) (hb : d131098 q = 1) : d765 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18865, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18865, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18866 q = 1) (hb : d131098 q = 1) : d16231 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18866, d16231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18866, d16231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18867 q = 1) (hb : d131098 q = 1) : d16283 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18867, d16283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18867, d16283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18878 q = 1) (hb : d131098 q = 1) : d18878 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d18879 q = 1) (hb : d131098 q = 1) : d188016 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18879, d188016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d18879, d188016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro42334 (p : Pattern) (ha : d18886 p = 1) (hb : d131098 p = 1) : d188019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18859 q = 1) (hb : d131098 q = 1) : d16228 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18859, d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42331 q ha hb
    | true =>
      simp only [d18859, d16228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42325 q ha hb
  have h2 (q : Pattern) (ha : d18860 q = 1) (hb : d131098 q = 1) : d16229 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18860, d16229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18860, d16229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18861 q = 1) (hb : d131098 q = 1) : d16230 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18861, d16230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18861, d16230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d18863 q = 1) (hb : d131098 q = 1) : d763 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d18863, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42325 q ha hb
    | true =>
      simp only [d18863, d763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42326 q ha hb
  have h5 (q : Pattern) (ha : d18864 q = 1) (hb : d131098 q = 1) : d764 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18864, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18864, d764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18865 q = 1) (hb : d131098 q = 1) : d765 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18865, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18865, d765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d18866 q = 1) (hb : d131098 q = 1) : d16231 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18866, d16231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18866, d16231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18882 q = 1) (hb : d131098 q = 1) : d767 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18882, d767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18882, d767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18883 q = 1) (hb : d131098 q = 1) : d16232 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18883, d16232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18883, d16232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18885 q = 1) (hb : d131098 q = 1) : d18885 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d18886 q = 1) (hb : d131098 q = 1) : d188019 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d18886, d188019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d18886, d188019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42335 (p : Pattern) (ha : d18892 p = 1) (hb : d131098 p = 1) : d188025 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18880 q = 1) (hb : d131098 q = 1) : d188017 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18880, d188017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42333 q ha hb
    | true =>
      simp only [d18880, d188017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18881 q = 1) (hb : d131098 q = 1) : d188018 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18881, d188018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18881, d188018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18887 q = 1) (hb : d131098 q = 1) : d188020 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18887, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42334 q ha hb
    | true =>
      simp only [d18887, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18888 q = 1) (hb : d131098 q = 1) : d188021 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18888, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18888, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18889 q = 1) (hb : d131098 q = 1) : d188022 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18889, d188022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18889, d188022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18890 q = 1) (hb : d131098 q = 1) : d188023 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18890, d188023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18890, d188023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18891 q = 1) (hb : d131098 q = 1) : d188024 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18891, d188024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18891, d188024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18892 q = 1) (hb : d131098 q = 1) : d188025 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18892, d188025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18892, d188025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42336 (p : Pattern) (ha : d18901 p = 1) (hb : d131098 p = 1) : d188032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18887 q = 1) (hb : d131098 q = 1) : d188020 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18887, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42334 q ha hb
    | true =>
      simp only [d18887, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18888 q = 1) (hb : d131098 q = 1) : d188021 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18888, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18888, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18896 q = 1) (hb : d131098 q = 1) : d188027 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18896, d188027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42327 q ha hb
    | true =>
      simp only [d18896, d188027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18897 q = 1) (hb : d131098 q = 1) : d188028 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18897, d188028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18897, d188028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d18898 q = 1) (hb : d131098 q = 1) : d188029 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18898, d188029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18898, d188029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d18899 q = 1) (hb : d131098 q = 1) : d188030 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18899, d188030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18899, d188030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18900 q = 1) (hb : d131098 q = 1) : d188031 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18900, d188031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18900, d188031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d18901 q = 1) (hb : d131098 q = 1) : d188032 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18901, d188032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18901, d188032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42337 (p : Pattern) (ha : d18959 p = 1) (hb : d131098 p = 1) : d188038 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18887 q = 1) (hb : d131098 q = 1) : d188020 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d18887, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42334 q ha hb
    | true =>
      simp only [d18887, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d18888 q = 1) (hb : d131098 q = 1) : d188021 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d18888, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18888, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d18956 q = 1) (hb : d131098 q = 1) : d188035 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d18956, d188035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18956, d188035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18957 q = 1) (hb : d131098 q = 1) : d188036 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d18957, d188036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18957, d188036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d18958 q = 1) (hb : d131098 q = 1) : d188037 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d18958, d188037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18958, d188037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18959 q = 1) (hb : d131098 q = 1) : d188038 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d18959, d188038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d18959, d188038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42338 (p : Pattern) (ha : d131098 p = 1) (hb : d132643 p = 1) : d188044 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18902 q = 1) (hb : d131098 q = 1) : d188033 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18902, d188033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42335 q ha hb
    | true =>
      simp only [d18902, d188033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42336 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132639 q = 1) : d188034 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132639, d188034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132639, d188034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d18960 q = 1) (hb : d131098 q = 1) : d188039 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18960, d188039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42337 q ha hb
    | true =>
      simp only [d18960, d188039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d18961 q = 1) (hb : d131098 q = 1) : d188040 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d18961, d188040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d18961, d188040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132640 q = 1) : d188041 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132640, d188041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132640, d188041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132641 q = 1) : d188042 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132641, d188042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132641, d188042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131098 q = 1) (hb : d132642 q = 1) : d188043 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132642, d188043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132642, d188043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131098 q = 1) (hb : d132643 q = 1) : d188044 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132643, d188044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132643, d188044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42339 (p : Pattern) (ha : d131098 p = 1) (hb : d132649 p = 1) : d188061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d132644 q = 1) : d188045 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132644, d188045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132644, d188045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42338 q ha hb
  have h2 (q : Pattern) (ha : d18977 q = 1) (hb : d131098 q = 1) : d188056 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18977, d188056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18977, d188056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42329 q ha hb
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d132645 q = 1) : d188057 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132645, d188057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132645, d188057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d132646 q = 1) : d188058 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132646, d188058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132646, d188058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132647 q = 1) : d188059 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132647, d188059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132647, d188059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132648 q = 1) : d188060 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132648, d188060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132648, d188060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131098 q = 1) (hb : d132649 q = 1) : d188061 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132649, d188061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132649, d188061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42340 (p : Pattern) (ha : d131098 p = 1) (hb : d132655 p = 1) : d188067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d132650 q = 1) : d188062 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132650, d188062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132650, d188062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42339 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132651 q = 1) : d188063 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132651, d188063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132651, d188063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d132652 q = 1) : d188064 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132652, d188064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132652, d188064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d132653 q = 1) : d188065 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132653, d188065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132653, d188065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132654 q = 1) : d188066 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132654, d188066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132654, d188066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132655 q = 1) : d188067 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132655, d188067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132655, d188067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42341 (p : Pattern) (ha : d19038 p = 1) (hb : d131098 p = 1) : d16443 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1109 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1385 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1385, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1385, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19031 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19031, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19031, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1111 q = 1) (hb : d131098 q = 1) : d1111 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19032 q = 1) (hb : d131098 q = 1) : d1112 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19032, d1112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19032, d1112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19033 q = 1) (hb : d131098 q = 1) : d1113 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19033, d1113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19033, d1113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d1120 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1391 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19034 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19034, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19034, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d1122 q = 1) (hb : d131098 q = 1) : d1122 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d19035 q = 1) (hb : d131098 q = 1) : d1123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19035, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19035, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19036 q = 1) (hb : d131098 q = 1) : d1124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19036, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19036, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d19037 q = 1) (hb : d131098 q = 1) : d1125 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19037, d1125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19037, d1125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d9799 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d15004 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d19013 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19013, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19013, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h19 (q : Pattern) (ha : d9802 q = 1) (hb : d131098 q = 1) : d9802 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d19014 q = 1) (hb : d131098 q = 1) : d14763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19014, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d19014, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d19015 q = 1) (hb : d131098 q = 1) : d14764 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19015, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19015, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h22 (q : Pattern) (ha : d19025 q = 1) (hb : d131098 q = 1) : d14765 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19025, d14765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d19025, d14765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h23 (q : Pattern) (ha : d19038 q = 1) (hb : d131098 q = 1) : d16443 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19038, d16443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19038, d16443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro42342 (p : Pattern) (ha : d19082 p = 1) (hb : d131098 p = 1) : d14778 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1391 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19034 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19034, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19034, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1122 q = 1) (hb : d131098 q = 1) : d1122 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19035 q = 1) (hb : d131098 q = 1) : d1123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19035, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19035, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19036 q = 1) (hb : d131098 q = 1) : d1124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19036, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19036, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19081 q = 1) (hb : d131098 q = 1) : d1127 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19081, d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19081, d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d9843 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15019 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d19046 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19046, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19046, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d9846 q = 1) (hb : d131098 q = 1) : d9846 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d19047 q = 1) (hb : d131098 q = 1) : d14770 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19047, d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19047, d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19048 q = 1) (hb : d131098 q = 1) : d14771 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19048, d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19048, d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d19049 q = 1) (hb : d131098 q = 1) : d14772 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19049, d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19049, d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h17 (q : Pattern) (ha : d19082 q = 1) (hb : d131098 q = 1) : d14778 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19082, d14778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19082, d14778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro42343 (p : Pattern) (ha : d19092 p = 1) (hb : d131098 p = 1) : d188080 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19083 q = 1) (hb : d131098 q = 1) : d16451 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19083, d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42341 q ha hb
    | true =>
      simp only [d19083, d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42342 q ha hb
  have h2 (q : Pattern) (ha : d19084 q = 1) (hb : d131098 q = 1) : d16452 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19084, d16452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19084, d16452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19085 q = 1) (hb : d131098 q = 1) : d16453 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19085, d16453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19085, d16453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19086 q = 1) (hb : d131098 q = 1) : d16454 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19086, d16454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19086, d16454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19087 q = 1) (hb : d131098 q = 1) : d16459 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19087, d16459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19087, d16459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19091 q = 1) (hb : d131098 q = 1) : d19091 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19092 q = 1) (hb : d131098 q = 1) : d188080 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19092, d188080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19092, d188080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42344 (p : Pattern) (ha : d19201 p = 1) (hb : d131098 p = 1) : d188106 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19093 q = 1) (hb : d131098 q = 1) : d188081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19093, d188081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42343 q ha hb
    | true =>
      simp only [d19093, d188081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19094 q = 1) (hb : d131098 q = 1) : d188082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19094, d188082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19094, d188082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19198 q = 1) (hb : d131098 q = 1) : d188103 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19198, d188103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19198, d188103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19199 q = 1) (hb : d131098 q = 1) : d188104 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19199, d188104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19199, d188104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19200 q = 1) (hb : d131098 q = 1) : d188105 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19200, d188105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19200, d188105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19201 q = 1) (hb : d131098 q = 1) : d188106 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19201, d188106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19201, d188106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42345 (p : Pattern) (ha : d19207 p = 1) (hb : d131098 p = 1) : d188112 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19202 q = 1) (hb : d131098 q = 1) : d188107 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19202, d188107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42344 q ha hb
    | true =>
      simp only [d19202, d188107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19203 q = 1) (hb : d131098 q = 1) : d188108 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19203, d188108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19203, d188108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19204 q = 1) (hb : d131098 q = 1) : d188109 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19204, d188109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19204, d188109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19205 q = 1) (hb : d131098 q = 1) : d188110 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19205, d188110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19205, d188110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19206 q = 1) (hb : d131098 q = 1) : d188111 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19206, d188111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19206, d188111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19207 q = 1) (hb : d131098 q = 1) : d188112 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19207, d188112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19207, d188112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42346 (p : Pattern) (ha : d19005 p = 1) (hb : d131098 p = 1) : d16511 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1209 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1376 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1376, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1376, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d18991 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18991, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d18991, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1211 q = 1) (hb : d131098 q = 1) : d1211 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d18992 q = 1) (hb : d131098 q = 1) : d1212 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18992, d1212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18992, d1212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d18993 q = 1) (hb : d131098 q = 1) : d1213 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18993, d1213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d18993, d1213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9752 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16649 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16649, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16649, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d18994 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18994, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d18994, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d9755 q = 1) (hb : d131098 q = 1) : d9755 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d18995 q = 1) (hb : d131098 q = 1) : d16507 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18995, d16507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18995, d16507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18996 q = 1) (hb : d131098 q = 1) : d16508 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d18996, d16508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18996, d16508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d18997 q = 1) (hb : d131098 q = 1) : d16509 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d18997, d16509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18997, d16509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d9762 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d14987 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14987, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14987, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d18998 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d18998, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18998, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h19 (q : Pattern) (ha : d9765 q = 1) (hb : d131098 q = 1) : d9765 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d18999 q = 1) (hb : d131098 q = 1) : d14836 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d18999, d14836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d18999, d14836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d19000 q = 1) (hb : d131098 q = 1) : d14837 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19000, d14837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19000, d14837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d9777 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d14994 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14994, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d19001 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19001, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d19001, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d9780 q = 1) (hb : d131098 q = 1) : d9780 q = 1 := by
    exact ha
  have h26 (q : Pattern) (ha : d19002 q = 1) (hb : d131098 q = 1) : d14758 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19002, d14758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d19002, d14758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d19003 q = 1) (hb : d131098 q = 1) : d14759 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19003, d14759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d19003, d14759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h28 (q : Pattern) (ha : d19004 q = 1) (hb : d131098 q = 1) : d16510 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19004, d16510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d19004, d16510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d19005 q = 1) (hb : d131098 q = 1) : d16511 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19005, d16511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19005, d16511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro42347 (p : Pattern) (ha : d19017 p = 1) (hb : d131098 p = 1) : d16442 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1380 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1380, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1380, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19006 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19006, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19006, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1101 q = 1) (hb : d131098 q = 1) : d1101 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19007 q = 1) (hb : d131098 q = 1) : d1102 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19007, d1102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19007, d1102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19008 q = 1) (hb : d131098 q = 1) : d1103 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19008, d1103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19008, d1103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9788 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d16656 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d16656, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16656, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19009 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19009, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19009, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d9791 q = 1) (hb : d131098 q = 1) : d9791 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d19010 q = 1) (hb : d131098 q = 1) : d16438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19010, d16438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19010, d16438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19011 q = 1) (hb : d131098 q = 1) : d16439 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19011, d16439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19011, d16439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d19012 q = 1) (hb : d131098 q = 1) : d16440 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19012, d16440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19012, d16440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d9777 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d14994 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d14994, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14994, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d19001 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19001, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19001, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h19 (q : Pattern) (ha : d9780 q = 1) (hb : d131098 q = 1) : d9780 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d19002 q = 1) (hb : d131098 q = 1) : d14758 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19002, d14758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d19002, d14758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d19003 q = 1) (hb : d131098 q = 1) : d14759 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19003, d14759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19003, d14759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d9799 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d15004 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d19013 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19013, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d19013, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d9802 q = 1) (hb : d131098 q = 1) : d9802 q = 1 := by
    exact ha
  have h26 (q : Pattern) (ha : d19014 q = 1) (hb : d131098 q = 1) : d14763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19014, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d19014, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d19015 q = 1) (hb : d131098 q = 1) : d14764 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19015, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d19015, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h28 (q : Pattern) (ha : d19016 q = 1) (hb : d131098 q = 1) : d16441 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19016, d16441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d19016, d16441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d19017 q = 1) (hb : d131098 q = 1) : d16442 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19017, d16442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19017, d16442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro42348 (p : Pattern) (ha : d19026 p = 1) (hb : d131098 p = 1) : d16516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d9813 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13160 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13160, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13160, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19021 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19021, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19021, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d9816 q = 1) (hb : d131098 q = 1) : d9816 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19022 q = 1) (hb : d131098 q = 1) : d13022 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19022, d13022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19022, d13022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19023 q = 1) (hb : d131098 q = 1) : d13023 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19023, d13023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19023, d13023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d9799 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15004 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15004, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15004, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19013 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19013, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19013, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d9802 q = 1) (hb : d131098 q = 1) : d9802 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d19014 q = 1) (hb : d131098 q = 1) : d14763 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19014, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19014, d14763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19015 q = 1) (hb : d131098 q = 1) : d14764 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19015, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19015, d14764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d19024 q = 1) (hb : d131098 q = 1) : d16515 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19024, d16515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19024, d16515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19025 q = 1) (hb : d131098 q = 1) : d14765 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19025, d14765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19025, d14765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h17 (q : Pattern) (ha : d19026 q = 1) (hb : d131098 q = 1) : d16516 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19026, d16516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19026, d16516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro42349 (p : Pattern) (ha : d19050 p = 1) (hb : d131098 p = 1) : d14773 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5017 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6350 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6350, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6350, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19042 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19042, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19042, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5019 q = 1) (hb : d131098 q = 1) : d5019 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19043 q = 1) (hb : d131098 q = 1) : d5020 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19043, d5020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19043, d5020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19044 q = 1) (hb : d131098 q = 1) : d5021 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19044, d5021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19044, d5021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19045 q = 1) (hb : d131098 q = 1) : d5022 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19045, d5022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19045, d5022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d9843 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15019 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d19046 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19046, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19046, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d9846 q = 1) (hb : d131098 q = 1) : d9846 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d19047 q = 1) (hb : d131098 q = 1) : d14770 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19047, d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19047, d14770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19048 q = 1) (hb : d131098 q = 1) : d14771 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19048, d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19048, d14771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d19049 q = 1) (hb : d131098 q = 1) : d14772 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19049, d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19049, d14772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h17 (q : Pattern) (ha : d19050 q = 1) (hb : d131098 q = 1) : d14773 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19050, d14773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19050, d14773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro42350 (p : Pattern) (ha : d19067 p = 1) (hb : d131098 p = 1) : d188070 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19018 q = 1) (hb : d131098 q = 1) : d16512 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19018, d16512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42346 q ha hb
    | true =>
      simp only [d19018, d16512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42347 q ha hb
  have h2 (q : Pattern) (ha : d19019 q = 1) (hb : d131098 q = 1) : d16513 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19019, d16513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19019, d16513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19020 q = 1) (hb : d131098 q = 1) : d16514 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19020, d16514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19020, d16514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19027 q = 1) (hb : d131098 q = 1) : d16517 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19027, d16517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42347 q ha hb
    | true =>
      simp only [d19027, d16517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42348 q ha hb
  have h5 (q : Pattern) (ha : d19028 q = 1) (hb : d131098 q = 1) : d16518 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19028, d16518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19028, d16518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19029 q = 1) (hb : d131098 q = 1) : d16519 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19029, d16519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19029, d16519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19030 q = 1) (hb : d131098 q = 1) : d16520 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19030, d16520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19030, d16520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19039 q = 1) (hb : d131098 q = 1) : d16444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19039, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42347 q ha hb
    | true =>
      simp only [d19039, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42341 q ha hb
  have h9 (q : Pattern) (ha : d19040 q = 1) (hb : d131098 q = 1) : d16445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19040, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19040, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19041 q = 1) (hb : d131098 q = 1) : d16446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19041, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19041, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19051 q = 1) (hb : d131098 q = 1) : d16447 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19051, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42341 q ha hb
    | true =>
      simp only [d19051, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42349 q ha hb
  have h12 (q : Pattern) (ha : d19052 q = 1) (hb : d131098 q = 1) : d16448 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19052, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19052, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19053 q = 1) (hb : d131098 q = 1) : d16449 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19053, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19053, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19054 q = 1) (hb : d131098 q = 1) : d16450 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19054, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19054, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19055 q = 1) (hb : d131098 q = 1) : d16521 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19055, d16521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19055, d16521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19066 q = 1) (hb : d131098 q = 1) : d19066 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d19067 q = 1) (hb : d131098 q = 1) : d188070 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19067, d188070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19067, d188070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro42351 (p : Pattern) (ha : d19074 p = 1) (hb : d131098 p = 1) : d188073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19039 q = 1) (hb : d131098 q = 1) : d16444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19039, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42347 q ha hb
    | true =>
      simp only [d19039, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42341 q ha hb
  have h2 (q : Pattern) (ha : d19040 q = 1) (hb : d131098 q = 1) : d16445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19040, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19040, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19041 q = 1) (hb : d131098 q = 1) : d16446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19041, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19041, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19051 q = 1) (hb : d131098 q = 1) : d16447 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19051, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42341 q ha hb
    | true =>
      simp only [d19051, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42349 q ha hb
  have h5 (q : Pattern) (ha : d19052 q = 1) (hb : d131098 q = 1) : d16448 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19052, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19052, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19053 q = 1) (hb : d131098 q = 1) : d16449 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19053, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19053, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19054 q = 1) (hb : d131098 q = 1) : d16450 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19054, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19054, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19070 q = 1) (hb : d131098 q = 1) : d16525 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19070, d16525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19070, d16525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19071 q = 1) (hb : d131098 q = 1) : d16526 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19071, d16526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19071, d16526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19073 q = 1) (hb : d131098 q = 1) : d19073 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d19074 q = 1) (hb : d131098 q = 1) : d188073 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19074, d188073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19074, d188073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42352 (p : Pattern) (ha : d19080 p = 1) (hb : d131098 p = 1) : d188079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19068 q = 1) (hb : d131098 q = 1) : d188071 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19068, d188071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42350 q ha hb
    | true =>
      simp only [d19068, d188071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19069 q = 1) (hb : d131098 q = 1) : d188072 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19069, d188072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19069, d188072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19075 q = 1) (hb : d131098 q = 1) : d188074 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19075, d188074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42351 q ha hb
    | true =>
      simp only [d19075, d188074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19076 q = 1) (hb : d131098 q = 1) : d188075 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19076, d188075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19076, d188075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19077 q = 1) (hb : d131098 q = 1) : d188076 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19077, d188076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19077, d188076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19078 q = 1) (hb : d131098 q = 1) : d188077 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19078, d188077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19078, d188077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19079 q = 1) (hb : d131098 q = 1) : d188078 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19079, d188078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19079, d188078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19080 q = 1) (hb : d131098 q = 1) : d188079 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19080, d188079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19080, d188079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42353 (p : Pattern) (ha : d19098 p = 1) (hb : d131098 p = 1) : d188086 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19075 q = 1) (hb : d131098 q = 1) : d188074 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19075, d188074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42351 q ha hb
    | true =>
      simp only [d19075, d188074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19076 q = 1) (hb : d131098 q = 1) : d188075 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19076, d188075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19076, d188075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19093 q = 1) (hb : d131098 q = 1) : d188081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19093, d188081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42343 q ha hb
    | true =>
      simp only [d19093, d188081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19094 q = 1) (hb : d131098 q = 1) : d188082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19094, d188082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19094, d188082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19095 q = 1) (hb : d131098 q = 1) : d188083 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19095, d188083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19095, d188083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19096 q = 1) (hb : d131098 q = 1) : d188084 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19096, d188084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19096, d188084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19097 q = 1) (hb : d131098 q = 1) : d188085 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19097, d188085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19097, d188085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19098 q = 1) (hb : d131098 q = 1) : d188086 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19098, d188086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19098, d188086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42354 (p : Pattern) (ha : d19174 p = 1) (hb : d131098 p = 1) : d12961 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1120 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1391 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1391, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1391, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19034 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19034, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19034, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1122 q = 1) (hb : d131098 q = 1) : d1122 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19035 q = 1) (hb : d131098 q = 1) : d1123 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19035, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19035, d1123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19036 q = 1) (hb : d131098 q = 1) : d1124 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19036, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19036, d1124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19081 q = 1) (hb : d131098 q = 1) : d1127 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19081, d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19081, d1127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d19174 q = 1) (hb : d131098 q = 1) : d12961 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19174, d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19174, d12961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h10 p ha hb
theorem andIntro42355 (p : Pattern) (ha : d19184 p = 1) (hb : d131098 p = 1) : d188089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19039 q = 1) (hb : d131098 q = 1) : d16444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19039, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42347 q ha hb
    | true =>
      simp only [d19039, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42341 q ha hb
  have h2 (q : Pattern) (ha : d19040 q = 1) (hb : d131098 q = 1) : d16445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19040, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19040, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19041 q = 1) (hb : d131098 q = 1) : d16446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19041, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19041, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19051 q = 1) (hb : d131098 q = 1) : d16447 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19051, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42341 q ha hb
    | true =>
      simp only [d19051, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42349 q ha hb
  have h5 (q : Pattern) (ha : d19052 q = 1) (hb : d131098 q = 1) : d16448 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19052, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19052, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19053 q = 1) (hb : d131098 q = 1) : d16449 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19053, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19053, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19054 q = 1) (hb : d131098 q = 1) : d16450 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19054, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19054, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19175 q = 1) (hb : d131098 q = 1) : d16574 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19175, d16574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42341 q ha hb
    | true =>
      simp only [d19175, d16574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42354 q ha hb
  have h9 (q : Pattern) (ha : d19176 q = 1) (hb : d131098 q = 1) : d16575 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19176, d16575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19176, d16575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19177 q = 1) (hb : d131098 q = 1) : d16576 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19177, d16576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19177, d16576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19178 q = 1) (hb : d131098 q = 1) : d16577 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19178, d16577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19178, d16577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d19179 q = 1) (hb : d131098 q = 1) : d16578 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19179, d16578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19179, d16578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19183 q = 1) (hb : d131098 q = 1) : d19183 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d19184 q = 1) (hb : d131098 q = 1) : d188089 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19184, d188089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19184, d188089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro42356 (p : Pattern) (ha : d19190 p = 1) (hb : d131098 p = 1) : d188095 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19185 q = 1) (hb : d131098 q = 1) : d188090 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19185, d188090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42355 q ha hb
    | true =>
      simp only [d19185, d188090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19186 q = 1) (hb : d131098 q = 1) : d188091 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19186, d188091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19186, d188091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19187 q = 1) (hb : d131098 q = 1) : d188092 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19187, d188092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19187, d188092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19188 q = 1) (hb : d131098 q = 1) : d188093 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19188, d188093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19188, d188093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19189 q = 1) (hb : d131098 q = 1) : d188094 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19189, d188094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19189, d188094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19190 q = 1) (hb : d131098 q = 1) : d188095 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19190, d188095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19190, d188095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42357 (p : Pattern) (ha : d131098 p = 1) (hb : d132662 p = 1) : d188101 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19099 q = 1) (hb : d131098 q = 1) : d188087 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19099, d188087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42352 q ha hb
    | true =>
      simp only [d19099, d188087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42353 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132658 q = 1) : d188088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132658, d188088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132658, d188088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d19191 q = 1) (hb : d131098 q = 1) : d188096 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19191, d188096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42356 q ha hb
    | true =>
      simp only [d19191, d188096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19192 q = 1) (hb : d131098 q = 1) : d188097 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19192, d188097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19192, d188097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132659 q = 1) : d188098 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132659, d188098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132659, d188098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132660 q = 1) : d188099 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132660, d188099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132660, d188099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131098 q = 1) (hb : d132661 q = 1) : d188100 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132661, d188100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132661, d188100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131098 q = 1) (hb : d132662 q = 1) : d188101 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132662, d188101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132662, d188101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42358 (p : Pattern) (ha : d131098 p = 1) (hb : d132668 p = 1) : d188118 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d132663 q = 1) : d188102 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132663, d188102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132663, d188102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42357 q ha hb
  have h2 (q : Pattern) (ha : d19208 q = 1) (hb : d131098 q = 1) : d188113 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19208, d188113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19208, d188113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42345 q ha hb
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d132664 q = 1) : d188114 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132664, d188114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132664, d188114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d132665 q = 1) : d188115 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132665, d188115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132665, d188115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132666 q = 1) : d188116 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132666, d188116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132666, d188116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132667 q = 1) : d188117 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132667, d188117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132667, d188117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131098 q = 1) (hb : d132668 q = 1) : d188118 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132668, d188118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132668, d188118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42359 (p : Pattern) (ha : d131098 p = 1) (hb : d132674 p = 1) : d188124 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d132669 q = 1) : d188119 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132669, d188119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132669, d188119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42358 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132670 q = 1) : d188120 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132670, d188120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132670, d188120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d132671 q = 1) : d188121 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132671, d188121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132671, d188121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d132672 q = 1) : d188122 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132672, d188122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132672, d188122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132673 q = 1) : d188123 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132673, d188123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132673, d188123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132674 q = 1) : d188124 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132674, d188124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132674, d188124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42360 (p : Pattern) (ha : d19270 p = 1) (hb : d131098 p = 1) : d16795 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1569 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1862 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1862, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1862, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19263 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19263, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19263, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1571 q = 1) (hb : d131098 q = 1) : d1571 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19264 q = 1) (hb : d131098 q = 1) : d1572 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19264, d1572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19264, d1572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19265 q = 1) (hb : d131098 q = 1) : d1573 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19265, d1573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19265, d1573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10114 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17027 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17027, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17027, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19266 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19266, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19266, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d10117 q = 1) (hb : d131098 q = 1) : d10117 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d19267 q = 1) (hb : d131098 q = 1) : d16792 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19267, d16792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19267, d16792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19268 q = 1) (hb : d131098 q = 1) : d16793 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19268, d16793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19268, d16793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d19269 q = 1) (hb : d131098 q = 1) : d16794 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19269, d16794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19269, d16794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d10084 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d15397 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d19245 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19245, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19245, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h19 (q : Pattern) (ha : d10087 q = 1) (hb : d131098 q = 1) : d10087 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d19246 q = 1) (hb : d131098 q = 1) : d15156 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19246, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d19246, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d19247 q = 1) (hb : d131098 q = 1) : d15157 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19247, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19247, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h22 (q : Pattern) (ha : d19257 q = 1) (hb : d131098 q = 1) : d15158 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19257, d15158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d19257, d15158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h23 (q : Pattern) (ha : d19270 q = 1) (hb : d131098 q = 1) : d16795 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19270, d16795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19270, d16795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro42361 (p : Pattern) (ha : d19317 p = 1) (hb : d131098 p = 1) : d15171 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1581 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1868 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19313 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19313, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19313, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1583 q = 1) (hb : d131098 q = 1) : d1583 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19314 q = 1) (hb : d131098 q = 1) : d1584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19314, d1584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19314, d1584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19315 q = 1) (hb : d131098 q = 1) : d1585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19315, d1585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19315, d1585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19316 q = 1) (hb : d131098 q = 1) : d1588 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19316, d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19316, d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10134 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15412 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d19278 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19278, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19278, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d10137 q = 1) (hb : d131098 q = 1) : d10137 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d19279 q = 1) (hb : d131098 q = 1) : d15163 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19279, d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19279, d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19280 q = 1) (hb : d131098 q = 1) : d15164 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19280, d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19280, d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d19281 q = 1) (hb : d131098 q = 1) : d15165 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19281, d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19281, d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h17 (q : Pattern) (ha : d19317 q = 1) (hb : d131098 q = 1) : d15171 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19317, d15171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19317, d15171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro42362 (p : Pattern) (ha : d19327 p = 1) (hb : d131098 p = 1) : d188138 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19318 q = 1) (hb : d131098 q = 1) : d16803 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19318, d16803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42360 q ha hb
    | true =>
      simp only [d19318, d16803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42361 q ha hb
  have h2 (q : Pattern) (ha : d19319 q = 1) (hb : d131098 q = 1) : d16804 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19319, d16804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19319, d16804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19320 q = 1) (hb : d131098 q = 1) : d16805 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19320, d16805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19320, d16805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19321 q = 1) (hb : d131098 q = 1) : d16806 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19321, d16806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19321, d16806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19322 q = 1) (hb : d131098 q = 1) : d16811 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19322, d16811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19322, d16811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19326 q = 1) (hb : d131098 q = 1) : d19326 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19327 q = 1) (hb : d131098 q = 1) : d188138 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19327, d188138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19327, d188138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42363 (p : Pattern) (ha : d19439 p = 1) (hb : d131098 p = 1) : d188164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19328 q = 1) (hb : d131098 q = 1) : d188139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19328, d188139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42362 q ha hb
    | true =>
      simp only [d19328, d188139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19329 q = 1) (hb : d131098 q = 1) : d188140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19329, d188140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19329, d188140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19436 q = 1) (hb : d131098 q = 1) : d188161 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19436, d188161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19436, d188161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19437 q = 1) (hb : d131098 q = 1) : d188162 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19437, d188162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19437, d188162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19438 q = 1) (hb : d131098 q = 1) : d188163 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19438, d188163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19438, d188163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19439 q = 1) (hb : d131098 q = 1) : d188164 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19439, d188164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19439, d188164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42364 (p : Pattern) (ha : d19445 p = 1) (hb : d131098 p = 1) : d188170 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19440 q = 1) (hb : d131098 q = 1) : d188165 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19440, d188165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42363 q ha hb
    | true =>
      simp only [d19440, d188165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19441 q = 1) (hb : d131098 q = 1) : d188166 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19441, d188166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19441, d188166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19442 q = 1) (hb : d131098 q = 1) : d188167 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19442, d188167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19442, d188167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19443 q = 1) (hb : d131098 q = 1) : d188168 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19443, d188168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19443, d188168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19444 q = 1) (hb : d131098 q = 1) : d188169 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19444, d188169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19444, d188169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19445 q = 1) (hb : d131098 q = 1) : d188170 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19445, d188170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19445, d188170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42365 (p : Pattern) (ha : d19237 p = 1) (hb : d131098 p = 1) : d16863 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1664 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1853 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1853, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1853, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19223 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19223, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19223, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1666 q = 1) (hb : d131098 q = 1) : d1666 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19224 q = 1) (hb : d131098 q = 1) : d1667 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19224, d1667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19224, d1667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19225 q = 1) (hb : d131098 q = 1) : d1668 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19225, d1668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19225, d1668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10035 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17004 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17004, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19226 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19226, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19226, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d10038 q = 1) (hb : d131098 q = 1) : d10038 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d19227 q = 1) (hb : d131098 q = 1) : d16859 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19227, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19227, d16859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19228 q = 1) (hb : d131098 q = 1) : d16860 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19228, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19228, d16860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d19229 q = 1) (hb : d131098 q = 1) : d16861 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19229, d16861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19229, d16861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d10045 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d15380 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15380, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15380, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d19230 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19230, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19230, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h19 (q : Pattern) (ha : d10048 q = 1) (hb : d131098 q = 1) : d10048 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d19231 q = 1) (hb : d131098 q = 1) : d15229 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19231, d15229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d19231, d15229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d19232 q = 1) (hb : d131098 q = 1) : d15230 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19232, d15230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19232, d15230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d10062 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d15387 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15387, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d19233 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19233, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d19233, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d10065 q = 1) (hb : d131098 q = 1) : d10065 q = 1 := by
    exact ha
  have h26 (q : Pattern) (ha : d19234 q = 1) (hb : d131098 q = 1) : d15151 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19234, d15151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d19234, d15151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d19235 q = 1) (hb : d131098 q = 1) : d15152 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19235, d15152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d19235, d15152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h28 (q : Pattern) (ha : d19236 q = 1) (hb : d131098 q = 1) : d16862 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19236, d16862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d19236, d16862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d19237 q = 1) (hb : d131098 q = 1) : d16863 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19237, d16863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19237, d16863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro42366 (p : Pattern) (ha : d19249 p = 1) (hb : d131098 p = 1) : d16791 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1554 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1857 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1857, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1857, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19238 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19238, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19238, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1556 q = 1) (hb : d131098 q = 1) : d1556 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19239 q = 1) (hb : d131098 q = 1) : d1557 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19239, d1557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19239, d1557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19240 q = 1) (hb : d131098 q = 1) : d1558 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19240, d1558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19240, d1558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10073 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17011 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17011, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17011, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19241 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19241, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19241, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d10076 q = 1) (hb : d131098 q = 1) : d10076 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d19242 q = 1) (hb : d131098 q = 1) : d16787 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19242, d16787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19242, d16787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19243 q = 1) (hb : d131098 q = 1) : d16788 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19243, d16788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19243, d16788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d19244 q = 1) (hb : d131098 q = 1) : d16789 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19244, d16789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19244, d16789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d10062 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d15387 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15387, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15387, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d19233 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19233, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19233, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h19 (q : Pattern) (ha : d10065 q = 1) (hb : d131098 q = 1) : d10065 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d19234 q = 1) (hb : d131098 q = 1) : d15151 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19234, d15151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d19234, d15151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d19235 q = 1) (hb : d131098 q = 1) : d15152 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19235, d15152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19235, d15152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d10084 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d15397 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d19245 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19245, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d19245, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d10087 q = 1) (hb : d131098 q = 1) : d10087 q = 1 := by
    exact ha
  have h26 (q : Pattern) (ha : d19246 q = 1) (hb : d131098 q = 1) : d15156 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19246, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d19246, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d19247 q = 1) (hb : d131098 q = 1) : d15157 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19247, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d19247, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h28 (q : Pattern) (ha : d19248 q = 1) (hb : d131098 q = 1) : d16790 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19248, d16790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d19248, d16790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d19249 q = 1) (hb : d131098 q = 1) : d16791 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19249, d16791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19249, d16791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro42367 (p : Pattern) (ha : d19258 p = 1) (hb : d131098 p = 1) : d16868 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13486 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13486, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13486, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19253 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19253, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19253, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10101 q = 1) (hb : d131098 q = 1) : d10101 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19254 q = 1) (hb : d131098 q = 1) : d13348 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19254, d13348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19254, d13348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19255 q = 1) (hb : d131098 q = 1) : d13349 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19255, d13349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19255, d13349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10084 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15397 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15397, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15397, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19245 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19245, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19245, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d10087 q = 1) (hb : d131098 q = 1) : d10087 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d19246 q = 1) (hb : d131098 q = 1) : d15156 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19246, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19246, d15156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19247 q = 1) (hb : d131098 q = 1) : d15157 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19247, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19247, d15157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d19256 q = 1) (hb : d131098 q = 1) : d16867 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19256, d16867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19256, d16867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19257 q = 1) (hb : d131098 q = 1) : d15158 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19257, d15158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19257, d15158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h17 (q : Pattern) (ha : d19258 q = 1) (hb : d131098 q = 1) : d16868 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19258, d16868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19258, d16868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro42368 (p : Pattern) (ha : d19282 p = 1) (hb : d131098 p = 1) : d15166 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5133 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6496 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6496, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6496, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19274 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19274, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19274, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5135 q = 1) (hb : d131098 q = 1) : d5135 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19275 q = 1) (hb : d131098 q = 1) : d5136 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19275, d5136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19275, d5136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19276 q = 1) (hb : d131098 q = 1) : d5137 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19276, d5137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19276, d5137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19277 q = 1) (hb : d131098 q = 1) : d5138 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19277, d5138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19277, d5138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10134 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15412 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d19278 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19278, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19278, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d10137 q = 1) (hb : d131098 q = 1) : d10137 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d19279 q = 1) (hb : d131098 q = 1) : d15163 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19279, d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19279, d15163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19280 q = 1) (hb : d131098 q = 1) : d15164 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19280, d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19280, d15164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d19281 q = 1) (hb : d131098 q = 1) : d15165 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19281, d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19281, d15165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h17 (q : Pattern) (ha : d19282 q = 1) (hb : d131098 q = 1) : d15166 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19282, d15166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19282, d15166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro42369 (p : Pattern) (ha : d19299 p = 1) (hb : d131098 p = 1) : d188128 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19250 q = 1) (hb : d131098 q = 1) : d16864 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19250, d16864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42365 q ha hb
    | true =>
      simp only [d19250, d16864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42366 q ha hb
  have h2 (q : Pattern) (ha : d19251 q = 1) (hb : d131098 q = 1) : d16865 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19251, d16865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19251, d16865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19252 q = 1) (hb : d131098 q = 1) : d16866 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19252, d16866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19252, d16866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19259 q = 1) (hb : d131098 q = 1) : d16869 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19259, d16869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42366 q ha hb
    | true =>
      simp only [d19259, d16869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42367 q ha hb
  have h5 (q : Pattern) (ha : d19260 q = 1) (hb : d131098 q = 1) : d16870 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19260, d16870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19260, d16870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19261 q = 1) (hb : d131098 q = 1) : d16871 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19261, d16871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19261, d16871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19262 q = 1) (hb : d131098 q = 1) : d16872 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19262, d16872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19262, d16872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19271 q = 1) (hb : d131098 q = 1) : d16796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19271, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42366 q ha hb
    | true =>
      simp only [d19271, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42360 q ha hb
  have h9 (q : Pattern) (ha : d19272 q = 1) (hb : d131098 q = 1) : d16797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19272, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19272, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19273 q = 1) (hb : d131098 q = 1) : d16798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19273, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19273, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19283 q = 1) (hb : d131098 q = 1) : d16799 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19283, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42360 q ha hb
    | true =>
      simp only [d19283, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42368 q ha hb
  have h12 (q : Pattern) (ha : d19284 q = 1) (hb : d131098 q = 1) : d16800 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19284, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19284, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19285 q = 1) (hb : d131098 q = 1) : d16801 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19285, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19285, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19286 q = 1) (hb : d131098 q = 1) : d16802 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19286, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19286, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19287 q = 1) (hb : d131098 q = 1) : d16873 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19287, d16873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19287, d16873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19298 q = 1) (hb : d131098 q = 1) : d19298 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d19299 q = 1) (hb : d131098 q = 1) : d188128 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19299, d188128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19299, d188128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro42370 (p : Pattern) (ha : d19306 p = 1) (hb : d131098 p = 1) : d188131 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19271 q = 1) (hb : d131098 q = 1) : d16796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19271, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42366 q ha hb
    | true =>
      simp only [d19271, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42360 q ha hb
  have h2 (q : Pattern) (ha : d19272 q = 1) (hb : d131098 q = 1) : d16797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19272, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19272, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19273 q = 1) (hb : d131098 q = 1) : d16798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19273, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19273, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19283 q = 1) (hb : d131098 q = 1) : d16799 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19283, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42360 q ha hb
    | true =>
      simp only [d19283, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42368 q ha hb
  have h5 (q : Pattern) (ha : d19284 q = 1) (hb : d131098 q = 1) : d16800 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19284, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19284, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19285 q = 1) (hb : d131098 q = 1) : d16801 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19285, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19285, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19286 q = 1) (hb : d131098 q = 1) : d16802 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19286, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19286, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19302 q = 1) (hb : d131098 q = 1) : d16877 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19302, d16877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19302, d16877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19303 q = 1) (hb : d131098 q = 1) : d16878 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19303, d16878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19303, d16878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19305 q = 1) (hb : d131098 q = 1) : d19305 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d19306 q = 1) (hb : d131098 q = 1) : d188131 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19306, d188131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19306, d188131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42371 (p : Pattern) (ha : d19312 p = 1) (hb : d131098 p = 1) : d188137 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19300 q = 1) (hb : d131098 q = 1) : d188129 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19300, d188129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42369 q ha hb
    | true =>
      simp only [d19300, d188129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19301 q = 1) (hb : d131098 q = 1) : d188130 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19301, d188130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19301, d188130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19307 q = 1) (hb : d131098 q = 1) : d188132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19307, d188132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42370 q ha hb
    | true =>
      simp only [d19307, d188132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19308 q = 1) (hb : d131098 q = 1) : d188133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19308, d188133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19308, d188133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19309 q = 1) (hb : d131098 q = 1) : d188134 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19309, d188134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19309, d188134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19310 q = 1) (hb : d131098 q = 1) : d188135 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19310, d188135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19310, d188135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19311 q = 1) (hb : d131098 q = 1) : d188136 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19311, d188136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19311, d188136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19312 q = 1) (hb : d131098 q = 1) : d188137 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19312, d188137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19312, d188137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42372 (p : Pattern) (ha : d19333 p = 1) (hb : d131098 p = 1) : d188144 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19307 q = 1) (hb : d131098 q = 1) : d188132 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19307, d188132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42370 q ha hb
    | true =>
      simp only [d19307, d188132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19308 q = 1) (hb : d131098 q = 1) : d188133 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19308, d188133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19308, d188133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19328 q = 1) (hb : d131098 q = 1) : d188139 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19328, d188139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42362 q ha hb
    | true =>
      simp only [d19328, d188139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19329 q = 1) (hb : d131098 q = 1) : d188140 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19329, d188140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19329, d188140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19330 q = 1) (hb : d131098 q = 1) : d188141 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19330, d188141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19330, d188141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19331 q = 1) (hb : d131098 q = 1) : d188142 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19331, d188142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19331, d188142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19332 q = 1) (hb : d131098 q = 1) : d188143 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19332, d188143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19332, d188143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19333 q = 1) (hb : d131098 q = 1) : d188144 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19333, d188144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19333, d188144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42373 (p : Pattern) (ha : d19412 p = 1) (hb : d131098 p = 1) : d13287 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1581 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1868 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1868, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1868, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19313 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19313, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19313, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1583 q = 1) (hb : d131098 q = 1) : d1583 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19314 q = 1) (hb : d131098 q = 1) : d1584 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19314, d1584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19314, d1584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19315 q = 1) (hb : d131098 q = 1) : d1585 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19315, d1585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19315, d1585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19316 q = 1) (hb : d131098 q = 1) : d1588 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19316, d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19316, d1588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d19412 q = 1) (hb : d131098 q = 1) : d13287 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19412, d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19412, d13287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h10 p ha hb
theorem andIntro42374 (p : Pattern) (ha : d19422 p = 1) (hb : d131098 p = 1) : d188147 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19271 q = 1) (hb : d131098 q = 1) : d16796 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19271, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42366 q ha hb
    | true =>
      simp only [d19271, d16796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42360 q ha hb
  have h2 (q : Pattern) (ha : d19272 q = 1) (hb : d131098 q = 1) : d16797 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19272, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19272, d16797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19273 q = 1) (hb : d131098 q = 1) : d16798 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19273, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19273, d16798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19283 q = 1) (hb : d131098 q = 1) : d16799 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19283, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42360 q ha hb
    | true =>
      simp only [d19283, d16799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42368 q ha hb
  have h5 (q : Pattern) (ha : d19284 q = 1) (hb : d131098 q = 1) : d16800 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19284, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19284, d16800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19285 q = 1) (hb : d131098 q = 1) : d16801 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19285, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19285, d16801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19286 q = 1) (hb : d131098 q = 1) : d16802 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19286, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19286, d16802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19413 q = 1) (hb : d131098 q = 1) : d16929 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19413, d16929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42360 q ha hb
    | true =>
      simp only [d19413, d16929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42373 q ha hb
  have h9 (q : Pattern) (ha : d19414 q = 1) (hb : d131098 q = 1) : d16930 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19414, d16930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19414, d16930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19415 q = 1) (hb : d131098 q = 1) : d16931 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19415, d16931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19415, d16931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19416 q = 1) (hb : d131098 q = 1) : d16932 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19416, d16932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19416, d16932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d19417 q = 1) (hb : d131098 q = 1) : d16933 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19417, d16933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19417, d16933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19421 q = 1) (hb : d131098 q = 1) : d19421 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d19422 q = 1) (hb : d131098 q = 1) : d188147 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19422, d188147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19422, d188147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro42375 (p : Pattern) (ha : d19428 p = 1) (hb : d131098 p = 1) : d188153 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19423 q = 1) (hb : d131098 q = 1) : d188148 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19423, d188148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42374 q ha hb
    | true =>
      simp only [d19423, d188148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19424 q = 1) (hb : d131098 q = 1) : d188149 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19424, d188149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19424, d188149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19425 q = 1) (hb : d131098 q = 1) : d188150 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19425, d188150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19425, d188150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19426 q = 1) (hb : d131098 q = 1) : d188151 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19426, d188151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19426, d188151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19427 q = 1) (hb : d131098 q = 1) : d188152 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19427, d188152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19427, d188152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19428 q = 1) (hb : d131098 q = 1) : d188153 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19428, d188153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19428, d188153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42376 (p : Pattern) (ha : d131098 p = 1) (hb : d132682 p = 1) : d188159 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19334 q = 1) (hb : d131098 q = 1) : d188145 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19334, d188145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42371 q ha hb
    | true =>
      simp only [d19334, d188145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42372 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132678 q = 1) : d188146 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132678, d188146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132678, d188146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d19429 q = 1) (hb : d131098 q = 1) : d188154 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19429, d188154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42375 q ha hb
    | true =>
      simp only [d19429, d188154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19430 q = 1) (hb : d131098 q = 1) : d188155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19430, d188155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19430, d188155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132679 q = 1) : d188156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132679, d188156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132679, d188156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132680 q = 1) : d188157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132680, d188157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132680, d188157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131098 q = 1) (hb : d132681 q = 1) : d188158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132681, d188158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132681, d188158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131098 q = 1) (hb : d132682 q = 1) : d188159 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132682, d188159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132682, d188159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42377 (p : Pattern) (ha : d131098 p = 1) (hb : d132688 p = 1) : d188176 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d132683 q = 1) : d188160 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132683, d188160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132683, d188160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42376 q ha hb
  have h2 (q : Pattern) (ha : d19446 q = 1) (hb : d131098 q = 1) : d188171 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19446, d188171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19446, d188171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42364 q ha hb
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d132684 q = 1) : d188172 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132684, d188172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132684, d188172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d132685 q = 1) : d188173 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132685, d188173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132685, d188173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132686 q = 1) : d188174 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132686, d188174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132686, d188174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132687 q = 1) : d188175 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132687, d188175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132687, d188175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131098 q = 1) (hb : d132688 q = 1) : d188176 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132688, d188176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132688, d188176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42378 (p : Pattern) (ha : d131098 p = 1) (hb : d132694 p = 1) : d188182 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d132689 q = 1) : d188177 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132689, d188177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132689, d188177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42377 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132690 q = 1) : d188178 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132690, d188178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132690, d188178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d132691 q = 1) : d188179 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132691, d188179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132691, d188179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d132692 q = 1) : d188180 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132692, d188180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132692, d188180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132693 q = 1) : d188181 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132693, d188181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132693, d188181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132694 q = 1) : d188182 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132694, d188182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132694, d188182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42379 (p : Pattern) (ha : d19502 p = 1) (hb : d131098 p = 1) : d17161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2052 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2340 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2340, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19495 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19495, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19495, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2054 q = 1) (hb : d131098 q = 1) : d2054 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19496 q = 1) (hb : d131098 q = 1) : d2055 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19496, d2055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19496, d2055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19497 q = 1) (hb : d131098 q = 1) : d2056 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19497, d2056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19497, d2056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10390 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17391 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17391, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17391, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19498 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19498, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19498, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d10393 q = 1) (hb : d131098 q = 1) : d10393 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d19499 q = 1) (hb : d131098 q = 1) : d17158 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19499, d17158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19499, d17158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19500 q = 1) (hb : d131098 q = 1) : d17159 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19500, d17159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19500, d17159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d19501 q = 1) (hb : d131098 q = 1) : d17160 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19501, d17160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19501, d17160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d10370 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d15775 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d19481 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19481, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19481, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h19 (q : Pattern) (ha : d10373 q = 1) (hb : d131098 q = 1) : d10373 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d19482 q = 1) (hb : d131098 q = 1) : d15548 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19482, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d19482, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d19483 q = 1) (hb : d131098 q = 1) : d15549 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19483, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19483, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h22 (q : Pattern) (ha : d19489 q = 1) (hb : d131098 q = 1) : d15550 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19489, d15550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d19489, d15550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h23 (q : Pattern) (ha : d19502 q = 1) (hb : d131098 q = 1) : d17161 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19502, d17161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19502, d17161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro42380 (p : Pattern) (ha : d19549 p = 1) (hb : d131098 p = 1) : d15563 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2064 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2346 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19545 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19545, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19545, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2066 q = 1) (hb : d131098 q = 1) : d2066 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19546 q = 1) (hb : d131098 q = 1) : d2067 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19546, d2067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19546, d2067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19547 q = 1) (hb : d131098 q = 1) : d2068 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19547, d2068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19547, d2068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19548 q = 1) (hb : d131098 q = 1) : d2071 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19548, d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19548, d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10411 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15790 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d19510 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19510, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19510, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d10414 q = 1) (hb : d131098 q = 1) : d10414 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d19511 q = 1) (hb : d131098 q = 1) : d15555 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19511, d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19511, d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19512 q = 1) (hb : d131098 q = 1) : d15556 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19512, d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19512, d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d19513 q = 1) (hb : d131098 q = 1) : d15557 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19513, d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19513, d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h17 (q : Pattern) (ha : d19549 q = 1) (hb : d131098 q = 1) : d15563 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19549, d15563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19549, d15563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro42381 (p : Pattern) (ha : d19559 p = 1) (hb : d131098 p = 1) : d188197 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19550 q = 1) (hb : d131098 q = 1) : d17169 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19550, d17169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42379 q ha hb
    | true =>
      simp only [d19550, d17169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42380 q ha hb
  have h2 (q : Pattern) (ha : d19551 q = 1) (hb : d131098 q = 1) : d17170 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19551, d17170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19551, d17170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19552 q = 1) (hb : d131098 q = 1) : d17171 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19552, d17171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19552, d17171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19553 q = 1) (hb : d131098 q = 1) : d17172 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19553, d17172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19553, d17172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19554 q = 1) (hb : d131098 q = 1) : d17177 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19554, d17177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19554, d17177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19558 q = 1) (hb : d131098 q = 1) : d19558 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d19559 q = 1) (hb : d131098 q = 1) : d188197 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19559, d188197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19559, d188197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42382 (p : Pattern) (ha : d19671 p = 1) (hb : d131098 p = 1) : d188223 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19560 q = 1) (hb : d131098 q = 1) : d188198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19560, d188198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42381 q ha hb
    | true =>
      simp only [d19560, d188198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19561 q = 1) (hb : d131098 q = 1) : d188199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19561, d188199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19561, d188199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19668 q = 1) (hb : d131098 q = 1) : d188220 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19668, d188220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19668, d188220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19669 q = 1) (hb : d131098 q = 1) : d188221 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19669, d188221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19669, d188221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19670 q = 1) (hb : d131098 q = 1) : d188222 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19670, d188222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19670, d188222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19671 q = 1) (hb : d131098 q = 1) : d188223 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19671, d188223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19671, d188223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42383 (p : Pattern) (ha : d19677 p = 1) (hb : d131098 p = 1) : d188229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19672 q = 1) (hb : d131098 q = 1) : d188224 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19672, d188224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42382 q ha hb
    | true =>
      simp only [d19672, d188224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19673 q = 1) (hb : d131098 q = 1) : d188225 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19673, d188225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19673, d188225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19674 q = 1) (hb : d131098 q = 1) : d188226 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d19674, d188226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19674, d188226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19675 q = 1) (hb : d131098 q = 1) : d188227 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d19675, d188227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19675, d188227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19676 q = 1) (hb : d131098 q = 1) : d188228 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d19676, d188228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19676, d188228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19677 q = 1) (hb : d131098 q = 1) : d188229 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d19677, d188229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19677, d188229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42384 (p : Pattern) (ha : d19473 p = 1) (hb : d131098 p = 1) : d17229 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2143 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2331 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2331, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2331, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19462 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19462, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19462, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2145 q = 1) (hb : d131098 q = 1) : d2145 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19463 q = 1) (hb : d131098 q = 1) : d2146 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19463, d2146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19463, d2146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19464 q = 1) (hb : d131098 q = 1) : d2147 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19464, d2147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19464, d2147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10342 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17369 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17369, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19465 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19465, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19465, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d10345 q = 1) (hb : d131098 q = 1) : d10345 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d19466 q = 1) (hb : d131098 q = 1) : d17225 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19466, d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19466, d17225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19467 q = 1) (hb : d131098 q = 1) : d17226 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19467, d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19467, d17226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d19468 q = 1) (hb : d131098 q = 1) : d17227 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19468, d17227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19468, d17227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d10352 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d13813 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d19469 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19469, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19469, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h19 (q : Pattern) (ha : d10355 q = 1) (hb : d131098 q = 1) : d10355 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d19470 q = 1) (hb : d131098 q = 1) : d13675 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19470, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d19470, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d19471 q = 1) (hb : d131098 q = 1) : d13676 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19471, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19471, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h22 (q : Pattern) (ha : d19472 q = 1) (hb : d131098 q = 1) : d17228 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19472, d17228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19472, d17228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d19473 q = 1) (hb : d131098 q = 1) : d17229 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19473, d17229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19473, d17229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro42385 (p : Pattern) (ha : d19485 p = 1) (hb : d131098 p = 1) : d17157 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2034 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2335 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2335, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19474 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19474, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19474, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2036 q = 1) (hb : d131098 q = 1) : d2036 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19475 q = 1) (hb : d131098 q = 1) : d2037 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19475, d2037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19475, d2037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19476 q = 1) (hb : d131098 q = 1) : d2038 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19476, d2038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19476, d2038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10363 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d17376 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17376, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19477 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19477, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19477, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d10366 q = 1) (hb : d131098 q = 1) : d10366 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d19478 q = 1) (hb : d131098 q = 1) : d17153 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19478, d17153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19478, d17153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19479 q = 1) (hb : d131098 q = 1) : d17154 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19479, d17154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19479, d17154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d19480 q = 1) (hb : d131098 q = 1) : d17155 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19480, d17155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19480, d17155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d0 q = 1) (hb : d10352 q = 1) : d0 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d13813 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  have h18 (q : Pattern) (ha : d19469 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19469, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19469, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h19 (q : Pattern) (ha : d10355 q = 1) (hb : d131098 q = 1) : d10355 q = 1 := by
    exact ha
  have h20 (q : Pattern) (ha : d19470 q = 1) (hb : d131098 q = 1) : d13675 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19470, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d19470, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d19471 q = 1) (hb : d131098 q = 1) : d13676 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19471, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19471, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h22 (q : Pattern) (ha : d0 q = 1) (hb : d10370 q = 1) : d0 q = 1 := by
    exact ha
  have h23 (q : Pattern) (ha : d15775 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
  have h24 (q : Pattern) (ha : d19481 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19481, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d19481, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h25 (q : Pattern) (ha : d10373 q = 1) (hb : d131098 q = 1) : d10373 q = 1 := by
    exact ha
  have h26 (q : Pattern) (ha : d19482 q = 1) (hb : d131098 q = 1) : d15548 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19482, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d19482, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d19483 q = 1) (hb : d131098 q = 1) : d15549 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19483, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d19483, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h28 (q : Pattern) (ha : d19484 q = 1) (hb : d131098 q = 1) : d17156 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19484, d17156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d19484, d17156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d19485 q = 1) (hb : d131098 q = 1) : d17157 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19485, d17157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19485, d17157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro42386 (p : Pattern) (ha : d19490 p = 1) (hb : d131098 p = 1) : d17233 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d10352 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d13813 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19469 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19469, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19469, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10355 q = 1) (hb : d131098 q = 1) : d10355 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19470 q = 1) (hb : d131098 q = 1) : d13675 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19470, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19470, d13675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19471 q = 1) (hb : d131098 q = 1) : d13676 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19471, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19471, d13676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d10370 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d15775 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15775, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15775, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d19481 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19481, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19481, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h12 (q : Pattern) (ha : d10373 q = 1) (hb : d131098 q = 1) : d10373 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d19482 q = 1) (hb : d131098 q = 1) : d15548 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19482, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19482, d15548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19483 q = 1) (hb : d131098 q = 1) : d15549 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19483, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19483, d15549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h15 (q : Pattern) (ha : d19484 q = 1) (hb : d131098 q = 1) : d17156 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19484, d17156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19484, d17156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19489 q = 1) (hb : d131098 q = 1) : d15550 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19489, d15550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19489, d15550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h17 (q : Pattern) (ha : d19490 q = 1) (hb : d131098 q = 1) : d17233 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19490, d17233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19490, d17233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro42387 (p : Pattern) (ha : d19514 p = 1) (hb : d131098 p = 1) : d15558 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d5246 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d6643 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d6643, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d6643, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19506 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19506, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19506, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d5248 q = 1) (hb : d131098 q = 1) : d5248 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19507 q = 1) (hb : d131098 q = 1) : d5249 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19507, d5249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19507, d5249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19508 q = 1) (hb : d131098 q = 1) : d5250 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19508, d5250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19508, d5250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19509 q = 1) (hb : d131098 q = 1) : d5251 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19509, d5251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19509, d5251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d10411 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d15790 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d19510 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19510, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19510, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d10414 q = 1) (hb : d131098 q = 1) : d10414 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d19511 q = 1) (hb : d131098 q = 1) : d15555 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19511, d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19511, d15555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19512 q = 1) (hb : d131098 q = 1) : d15556 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19512, d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19512, d15556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h16 (q : Pattern) (ha : d19513 q = 1) (hb : d131098 q = 1) : d15557 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19513, d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19513, d15557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h17 (q : Pattern) (ha : d19514 q = 1) (hb : d131098 q = 1) : d15558 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19514, d15558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19514, d15558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro42388 (p : Pattern) (ha : d19531 p = 1) (hb : d131098 p = 1) : d188187 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19486 q = 1) (hb : d131098 q = 1) : d17230 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19486, d17230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42384 q ha hb
    | true =>
      simp only [d19486, d17230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42385 q ha hb
  have h2 (q : Pattern) (ha : d19487 q = 1) (hb : d131098 q = 1) : d17231 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19487, d17231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19487, d17231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19488 q = 1) (hb : d131098 q = 1) : d17232 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19488, d17232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19488, d17232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19491 q = 1) (hb : d131098 q = 1) : d17234 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19491, d17234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42385 q ha hb
    | true =>
      simp only [d19491, d17234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42386 q ha hb
  have h5 (q : Pattern) (ha : d19492 q = 1) (hb : d131098 q = 1) : d17235 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19492, d17235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19492, d17235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19493 q = 1) (hb : d131098 q = 1) : d17236 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19493, d17236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19493, d17236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19494 q = 1) (hb : d131098 q = 1) : d17237 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19494, d17237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19494, d17237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19503 q = 1) (hb : d131098 q = 1) : d17162 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19503, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42385 q ha hb
    | true =>
      simp only [d19503, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42379 q ha hb
  have h9 (q : Pattern) (ha : d19504 q = 1) (hb : d131098 q = 1) : d17163 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19504, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19504, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19505 q = 1) (hb : d131098 q = 1) : d17164 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19505, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19505, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19515 q = 1) (hb : d131098 q = 1) : d17165 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19515, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42379 q ha hb
    | true =>
      simp only [d19515, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42387 q ha hb
  have h12 (q : Pattern) (ha : d19516 q = 1) (hb : d131098 q = 1) : d17166 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19516, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19516, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19517 q = 1) (hb : d131098 q = 1) : d17167 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19517, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19517, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19518 q = 1) (hb : d131098 q = 1) : d17168 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19518, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19518, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19519 q = 1) (hb : d131098 q = 1) : d17238 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19519, d17238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19519, d17238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19530 q = 1) (hb : d131098 q = 1) : d19530 q = 1 := by
    exact ha
  have h17 (q : Pattern) (ha : d19531 q = 1) (hb : d131098 q = 1) : d188187 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19531, d188187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d19531, d188187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro42389 (p : Pattern) (ha : d19538 p = 1) (hb : d131098 p = 1) : d188190 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19503 q = 1) (hb : d131098 q = 1) : d17162 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19503, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42385 q ha hb
    | true =>
      simp only [d19503, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42379 q ha hb
  have h2 (q : Pattern) (ha : d19504 q = 1) (hb : d131098 q = 1) : d17163 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19504, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19504, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19505 q = 1) (hb : d131098 q = 1) : d17164 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19505, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19505, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19515 q = 1) (hb : d131098 q = 1) : d17165 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19515, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42379 q ha hb
    | true =>
      simp only [d19515, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42387 q ha hb
  have h5 (q : Pattern) (ha : d19516 q = 1) (hb : d131098 q = 1) : d17166 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19516, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19516, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19517 q = 1) (hb : d131098 q = 1) : d17167 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19517, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19517, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19518 q = 1) (hb : d131098 q = 1) : d17168 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19518, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19518, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19534 q = 1) (hb : d131098 q = 1) : d17242 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19534, d17242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19534, d17242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19535 q = 1) (hb : d131098 q = 1) : d17243 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19535, d17243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19535, d17243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19537 q = 1) (hb : d131098 q = 1) : d19537 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d19538 q = 1) (hb : d131098 q = 1) : d188190 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19538, d188190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19538, d188190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42390 (p : Pattern) (ha : d19544 p = 1) (hb : d131098 p = 1) : d188196 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19532 q = 1) (hb : d131098 q = 1) : d188188 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19532, d188188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42388 q ha hb
    | true =>
      simp only [d19532, d188188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19533 q = 1) (hb : d131098 q = 1) : d188189 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19533, d188189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19533, d188189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19539 q = 1) (hb : d131098 q = 1) : d188191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19539, d188191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42389 q ha hb
    | true =>
      simp only [d19539, d188191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19540 q = 1) (hb : d131098 q = 1) : d188192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19540, d188192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19540, d188192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19541 q = 1) (hb : d131098 q = 1) : d188193 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19541, d188193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19541, d188193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19542 q = 1) (hb : d131098 q = 1) : d188194 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19542, d188194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19542, d188194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19543 q = 1) (hb : d131098 q = 1) : d188195 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19543, d188195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19543, d188195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19544 q = 1) (hb : d131098 q = 1) : d188196 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19544, d188196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19544, d188196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42391 (p : Pattern) (ha : d19565 p = 1) (hb : d131098 p = 1) : d188203 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19539 q = 1) (hb : d131098 q = 1) : d188191 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19539, d188191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42389 q ha hb
    | true =>
      simp only [d19539, d188191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19540 q = 1) (hb : d131098 q = 1) : d188192 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19540, d188192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19540, d188192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19560 q = 1) (hb : d131098 q = 1) : d188198 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19560, d188198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42381 q ha hb
    | true =>
      simp only [d19560, d188198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19561 q = 1) (hb : d131098 q = 1) : d188199 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19561, d188199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19561, d188199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d19562 q = 1) (hb : d131098 q = 1) : d188200 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19562, d188200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19562, d188200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19563 q = 1) (hb : d131098 q = 1) : d188201 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19563, d188201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19563, d188201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19564 q = 1) (hb : d131098 q = 1) : d188202 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19564, d188202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19564, d188202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d19565 q = 1) (hb : d131098 q = 1) : d188203 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19565, d188203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19565, d188203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro42392 (p : Pattern) (ha : d19644 p = 1) (hb : d131098 p = 1) : d13614 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d2064 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2346 q = 1) (hb : d102052 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2346, d102052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d19545 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d19545, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19545, d131098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2066 q = 1) (hb : d131098 q = 1) : d2066 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d19546 q = 1) (hb : d131098 q = 1) : d2067 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d19546, d2067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19546, d2067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d19547 q = 1) (hb : d131098 q = 1) : d2068 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d19547, d2068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d19547, d2068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d19548 q = 1) (hb : d131098 q = 1) : d2071 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d19548, d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19548, d2071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h10 (q : Pattern) (ha : d19644 q = 1) (hb : d131098 q = 1) : d13614 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d19644, d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d19644, d13614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h10 p ha hb
theorem andIntro42393 (p : Pattern) (ha : d19654 p = 1) (hb : d131098 p = 1) : d188206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19503 q = 1) (hb : d131098 q = 1) : d17162 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19503, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42385 q ha hb
    | true =>
      simp only [d19503, d17162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42379 q ha hb
  have h2 (q : Pattern) (ha : d19504 q = 1) (hb : d131098 q = 1) : d17163 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19504, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19504, d17163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19505 q = 1) (hb : d131098 q = 1) : d17164 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19505, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19505, d17164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19515 q = 1) (hb : d131098 q = 1) : d17165 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19515, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42379 q ha hb
    | true =>
      simp only [d19515, d17165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42387 q ha hb
  have h5 (q : Pattern) (ha : d19516 q = 1) (hb : d131098 q = 1) : d17166 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19516, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19516, d17166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19517 q = 1) (hb : d131098 q = 1) : d17167 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19517, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19517, d17167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19518 q = 1) (hb : d131098 q = 1) : d17168 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19518, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19518, d17168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19645 q = 1) (hb : d131098 q = 1) : d17294 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19645, d17294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42379 q ha hb
    | true =>
      simp only [d19645, d17294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42392 q ha hb
  have h9 (q : Pattern) (ha : d19646 q = 1) (hb : d131098 q = 1) : d17295 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19646, d17295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19646, d17295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19647 q = 1) (hb : d131098 q = 1) : d17296 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19647, d17296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19647, d17296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19648 q = 1) (hb : d131098 q = 1) : d17297 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19648, d17297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19648, d17297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d19649 q = 1) (hb : d131098 q = 1) : d17298 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19649, d17298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19649, d17298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19653 q = 1) (hb : d131098 q = 1) : d19653 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d19654 q = 1) (hb : d131098 q = 1) : d188206 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d19654, d188206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d19654, d188206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro42394 (p : Pattern) (ha : d19660 p = 1) (hb : d131098 p = 1) : d188212 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19655 q = 1) (hb : d131098 q = 1) : d188207 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19655, d188207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42393 q ha hb
    | true =>
      simp only [d19655, d188207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d19656 q = 1) (hb : d131098 q = 1) : d188208 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19656, d188208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19656, d188208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19657 q = 1) (hb : d131098 q = 1) : d188209 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d19657, d188209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d19657, d188209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19658 q = 1) (hb : d131098 q = 1) : d188210 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d19658, d188210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19658, d188210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d19659 q = 1) (hb : d131098 q = 1) : d188211 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d19659, d188211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19659, d188211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19660 q = 1) (hb : d131098 q = 1) : d188212 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d19660, d188212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d19660, d188212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro42395 (p : Pattern) (ha : d131098 p = 1) (hb : d132703 p = 1) : d188218 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19566 q = 1) (hb : d131098 q = 1) : d188204 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19566, d188204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42390 q ha hb
    | true =>
      simp only [d19566, d188204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42391 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132699 q = 1) : d188205 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d132699, d188205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132699, d188205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d19661 q = 1) (hb : d131098 q = 1) : d188213 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d19661, d188213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42394 q ha hb
    | true =>
      simp only [d19661, d188213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19662 q = 1) (hb : d131098 q = 1) : d188214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d19662, d188214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19662, d188214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132700 q = 1) : d188215 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d132700, d188215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132700, d188215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132701 q = 1) : d188216 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d132701, d188216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132701, d188216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131098 q = 1) (hb : d132702 q = 1) : d188217 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d132702, d188217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132702, d188217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131098 q = 1) (hb : d132703 q = 1) : d188218 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d132703, d188218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132703, d188218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro42396 (p : Pattern) (ha : d131098 p = 1) (hb : d132709 p = 1) : d188235 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d132704 q = 1) : d188219 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d132704, d188219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132704, d188219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42395 q ha hb
  have h2 (q : Pattern) (ha : d19678 q = 1) (hb : d131098 q = 1) : d188230 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d19678, d188230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19678, d188230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42383 q ha hb
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d132705 q = 1) : d188231 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d132705, d188231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132705, d188231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d132706 q = 1) : d188232 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d132706, d188232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132706, d188232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132707 q = 1) : d188233 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d132707, d188233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132707, d188233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132708 q = 1) : d188234 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d132708, d188234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132708, d188234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131098 q = 1) (hb : d132709 q = 1) : d188235 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d132709, d188235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132709, d188235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42397 (p : Pattern) (ha : d131098 p = 1) (hb : d132715 p = 1) : d188241 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d132710 q = 1) : d188236 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d132710, d188236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132710, d188236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42396 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132711 q = 1) : d188237 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d132711, d188237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132711, d188237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d132712 q = 1) : d188238 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d132712, d188238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132712, d188238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d132713 q = 1) : d188239 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d132713, d188239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132713, d188239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132714 q = 1) : d188240 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d132714, d188240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132714, d188240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132715 q = 1) : d188241 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d132715, d188241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d132715, d188241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42398 (p : Pattern) (ha : d131098 p = 1) (hb : d132721 p = 1) : d188247 p = 1 := by
  have h0 (q : Pattern) (ha : d131098 q = 1) (hb : d132638 q = 1) : d188015 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132638, d188015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42311 q ha hb
    | true =>
      simp only [d132638, d188015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42324 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132656 q = 1) : d188068 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132656, d188068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132656, d188068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42340 q ha hb
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d132657 q = 1) : d188069 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132657, d188069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d132657, d188069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d132675 q = 1) : d188125 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132675, d188125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132675, d188125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42359 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132676 q = 1) : d188126 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132676, d188126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132676, d188126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132677 q = 1) : d188127 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d132677, d188127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132677, d188127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d131098 q = 1) (hb : d132695 q = 1) : d188183 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132695, d188183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132695, d188183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42378 q ha hb
  have h8 (q : Pattern) (ha : d131098 q = 1) (hb : d132696 q = 1) : d188184 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132696, d188184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132696, d188184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131098 q = 1) (hb : d132697 q = 1) : d188185 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d132697, d188185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132697, d188185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131098 q = 1) (hb : d132698 q = 1) : d188186 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d132698, d188186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d132698, d188186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131098 q = 1) (hb : d132716 q = 1) : d188242 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d132716, d188242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132716, d188242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42397 q ha hb
  have h12 (q : Pattern) (ha : d131098 q = 1) (hb : d132717 q = 1) : d188243 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d132717, d188243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132717, d188243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d131098 q = 1) (hb : d132718 q = 1) : d188244 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d132718, d188244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132718, d188244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d131098 q = 1) (hb : d132719 q = 1) : d188245 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d132719, d188245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d132719, d188245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d131098 q = 1) (hb : d132720 q = 1) : d188246 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d132720, d188246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d132720, d188246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d131098 q = 1) (hb : d132721 q = 1) : d188247 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d132721, d188247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d132721, d188247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro42399 (p : Pattern) (ha : d131098 p = 1) (hb : d132727 p = 1) : d188253 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d132722 q = 1) : d188248 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d132722, d188248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42398 q ha hb
    | true =>
      simp only [d132722, d188248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132723 q = 1) : d188249 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d132723, d188249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132723, d188249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d132724 q = 1) : d188250 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d132724, d188250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132724, d188250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d132725 q = 1) : d188251 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d132725, d188251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132725, d188251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132726 q = 1) : d188252 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d132726, d188252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132726, d188252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132727 q = 1) : d188253 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d132727, d188253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132727, d188253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42400 (p : Pattern) (ha : d131098 p = 1) (hb : d132733 p = 1) : d188259 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d132728 q = 1) : d188254 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d132728, d188254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42399 q ha hb
    | true =>
      simp only [d132728, d188254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132729 q = 1) : d188255 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d132729, d188255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132729, d188255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d132730 q = 1) : d188256 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d132730, d188256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132730, d188256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d132731 q = 1) : d188257 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d132731, d188257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132731, d188257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132732 q = 1) : d188258 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d132732, d188258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132732, d188258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132733 q = 1) : d188259 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d132733, d188259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132733, d188259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42401 (p : Pattern) (ha : d131098 p = 1) (hb : d132739 p = 1) : d188265 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d132734 q = 1) : d188260 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d132734, d188260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42400 q ha hb
    | true =>
      simp only [d132734, d188260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132735 q = 1) : d188261 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d132735, d188261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132735, d188261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d132736 q = 1) : d188262 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d132736, d188262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132736, d188262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d132737 q = 1) : d188263 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d132737, d188263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132737, d188263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132738 q = 1) : d188264 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d132738, d188264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132738, d188264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132739 q = 1) : d188265 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d132739, d188265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132739, d188265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42402 (p : Pattern) (ha : d131098 p = 1) (hb : d132745 p = 1) : d188271 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d132740 q = 1) : d188266 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d132740, d188266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42401 q ha hb
    | true =>
      simp only [d132740, d188266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132741 q = 1) : d188267 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d132741, d188267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132741, d188267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d132742 q = 1) : d188268 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d132742, d188268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132742, d188268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d132743 q = 1) : d188269 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d132743, d188269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132743, d188269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132744 q = 1) : d188270 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d132744, d188270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132744, d188270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132745 q = 1) : d188271 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d132745, d188271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132745, d188271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42403 (p : Pattern) (ha : d131098 p = 1) (hb : d132751 p = 1) : d188277 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d132746 q = 1) : d188272 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d132746, d188272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42402 q ha hb
    | true =>
      simp only [d132746, d188272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132747 q = 1) : d188273 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d132747, d188273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132747, d188273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d132748 q = 1) : d188274 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d132748, d188274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132748, d188274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d132749 q = 1) : d188275 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d132749, d188275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132749, d188275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132750 q = 1) : d188276 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d132750, d188276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132750, d188276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132751 q = 1) : d188277 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d132751, d188277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132751, d188277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42404 (p : Pattern) (ha : d131098 p = 1) (hb : d132757 p = 1) : d188283 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d132752 q = 1) : d188278 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d132752, d188278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42403 q ha hb
    | true =>
      simp only [d132752, d188278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132753 q = 1) : d188279 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d132753, d188279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132753, d188279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d132754 q = 1) : d188280 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d132754, d188280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132754, d188280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d132755 q = 1) : d188281 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d132755, d188281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132755, d188281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132756 q = 1) : d188282 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d132756, d188282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132756, d188282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132757 q = 1) : d188283 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d132757, d188283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132757, d188283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42405 (p : Pattern) (ha : d131098 p = 1) (hb : d132763 p = 1) : d188289 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d132758 q = 1) : d188284 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d132758, d188284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42404 q ha hb
    | true =>
      simp only [d132758, d188284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d132759 q = 1) : d188285 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d132759, d188285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d132759, d188285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d132760 q = 1) : d188286 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d132760, d188286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d132760, d188286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d132761 q = 1) : d188287 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d132761, d188287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d132761, d188287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d132762 q = 1) : d188288 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d132762, d188288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d132762, d188288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d132763 q = 1) : d188289 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d132763, d188289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d132763, d188289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42406 (p : Pattern) (ha : d129677 p = 1) (hb : d187879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d31 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42088 q ha hb
    | true =>
      simp only [d31, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d32 q = 1) (hb : d129673 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d129673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d129673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d33 q = 1) (hb : d129674 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d129674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d129674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d34 q = 1) (hb : d129675 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d129675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d34, d129675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d35 q = 1) (hb : d129676 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d35, d129676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d35, d129676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18544 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18544, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18544, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18545 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18545, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18545, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18546 q = 1) (hb : d100951 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18546, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18546, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18547 q = 1) (hb : d100952 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18547, d100952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18547, d100952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d129677 q = 1) (hb : d187879 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129677, d187879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d129677, d187879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro42407 (p : Pattern) (ha : d129683 p = 1) (hb : d187885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129678 q = 1) (hb : d187880 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129678, d187880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42406 q ha hb
    | true =>
      simp only [d129678, d187880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129679 q = 1) (hb : d187881 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129679, d187881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129679, d187881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129680 q = 1) (hb : d187882 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129680, d187882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129680, d187882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129681 q = 1) (hb : d187883 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129681, d187883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129681, d187883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129682 q = 1) (hb : d187884 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129682, d187884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129682, d187884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129683 q = 1) (hb : d187885 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129683, d187885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129683, d187885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42408 (p : Pattern) (ha : d129689 p = 1) (hb : d187891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129684 q = 1) (hb : d187886 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129684, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42407 q ha hb
    | true =>
      simp only [d129684, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129685 q = 1) (hb : d187887 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129685, d187887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129685, d187887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129686 q = 1) (hb : d187888 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129686, d187888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129686, d187888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129687 q = 1) (hb : d187889 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129687, d187889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129687, d187889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129688 q = 1) (hb : d187890 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129688, d187890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129688, d187890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129689 q = 1) (hb : d187891 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129689, d187891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129689, d187891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42409 (p : Pattern) (ha : d129695 p = 1) (hb : d187897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129690 q = 1) (hb : d187892 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129690, d187892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129690, d187892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42408 q ha hb
  have h2 (q : Pattern) (ha : d129691 q = 1) (hb : d187893 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129691, d187893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129691, d187893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129692 q = 1) (hb : d187894 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129692, d187894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129692, d187894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129693 q = 1) (hb : d187895 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129693, d187895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129693, d187895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129694 q = 1) (hb : d187896 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129694, d187896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129694, d187896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129695 q = 1) (hb : d187897 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129695, d187897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129695, d187897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42410 (p : Pattern) (ha : d129704 p = 1) (hb : d187902 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42094 q ha hb
    | true =>
      simp only [d145, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42088 q ha hb
  have h2 (q : Pattern) (ha : d146 q = 1) (hb : d129700 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d129700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d129700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147 q = 1) (hb : d129701 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d129701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d129701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d31 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42088 q ha hb
    | true =>
      simp only [d31, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d32 q = 1) (hb : d129673 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d129673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d129673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d33 q = 1) (hb : d129674 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d129674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d129674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148 q = 1) (hb : d129702 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d129702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148, d129702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d129675 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d129675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, d129675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d149 q = 1) (hb : d129703 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d149, d129703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d149, d129703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18581 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18581, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d18582 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18582, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18544 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18544, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18544, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d18545 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18545, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18545, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18583 q = 1) (hb : d100984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18583, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18583, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18546 q = 1) (hb : d100951 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18546, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18546, d100951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d18584 q = 1) (hb : d100985 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18584, d100985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d18584, d100985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d129704 q = 1) (hb : d187902 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129704, d187902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d129704, d187902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro42411 (p : Pattern) (ha : d129710 p = 1) (hb : d187908 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129705 q = 1) (hb : d187903 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129705, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42410 q ha hb
    | true =>
      simp only [d129705, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129706 q = 1) (hb : d187904 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129706, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129706, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129678 q = 1) (hb : d187880 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129678, d187880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42406 q ha hb
    | true =>
      simp only [d129678, d187880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129679 q = 1) (hb : d187881 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129679, d187881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129679, d187881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129707 q = 1) (hb : d187905 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129707, d187905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129707, d187905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129708 q = 1) (hb : d187906 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129708, d187906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129708, d187906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129709 q = 1) (hb : d187907 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129709, d187907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129709, d187907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129710 q = 1) (hb : d187908 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129710, d187908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129710, d187908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42412 (p : Pattern) (ha : d129716 p = 1) (hb : d187914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129711 q = 1) (hb : d187909 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129711, d187909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42411 q ha hb
    | true =>
      simp only [d129711, d187909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42407 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129684 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129712 q = 1) (hb : d187910 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129712, d187910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129712, d187910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129684 q = 1) (hb : d187886 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129684, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42407 q ha hb
    | true =>
      simp only [d129684, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129685 q = 1) (hb : d187887 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129685, d187887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129685, d187887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129713 q = 1) (hb : d187911 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129713, d187911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129713, d187911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129714 q = 1) (hb : d187912 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129714, d187912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129714, d187912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129715 q = 1) (hb : d187913 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129715, d187913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129715, d187913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129716 q = 1) (hb : d187914 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129716, d187914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129716, d187914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro42413 (p : Pattern) (ha : d129722 p = 1) (hb : d187920 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129717 q = 1) (hb : d187915 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129717, d187915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129717, d187915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42412 q ha hb
  have h2 (q : Pattern) (ha : d129718 q = 1) (hb : d187916 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129718, d187916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129718, d187916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d129719 q = 1) (hb : d187917 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129719, d187917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129719, d187917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129720 q = 1) (hb : d187918 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129720, d187918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129720, d187918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129721 q = 1) (hb : d187919 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129721, d187919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129721, d187919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129722 q = 1) (hb : d187920 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129722, d187920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129722, d187920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42414 (p : Pattern) (ha : d129732 p = 1) (hb : d187926 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42101 q ha hb
    | true =>
      simp only [d15967, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42094 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d129728 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d129728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d129728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d129729 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d129729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d129729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42094 q ha hb
    | true =>
      simp only [d145, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42088 q ha hb
  have h5 (q : Pattern) (ha : d146 q = 1) (hb : d129700 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d129700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d129700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147 q = 1) (hb : d129701 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d129701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d129701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15970 q = 1) (hb : d129730 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d129730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d129730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d100948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42088 q ha hb
    | true =>
      simp only [d31, d100948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d129673 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d129673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d129673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d129674 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d129674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d129674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148 q = 1) (hb : d129702 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148, d129702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148, d129702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d15971 q = 1) (hb : d129731 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d15971, d129731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d15971, d129731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d18645 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18645, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18645, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d18646 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18646, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18646, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18581 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18581, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d18582 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18582, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d18647 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18647, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d18647, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d18544 q = 1) (hb : d100949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18544, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18544, d100949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d18545 q = 1) (hb : d100950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18545, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18545, d100950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d18583 q = 1) (hb : d100984 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18583, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d18583, d100984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d18648 q = 1) (hb : d101026 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18648, d101026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18648, d101026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d129732 q = 1) (hb : d187926 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129732, d187926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d129732, d187926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  exact h22 p ha hb
theorem andIntro42415 (p : Pattern) (ha : d129738 p = 1) (hb : d187932 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129733 q = 1) (hb : d187927 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129733, d187927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42414 q ha hb
    | true =>
      simp only [d129733, d187927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129734 q = 1) (hb : d187928 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129734, d187928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129734, d187928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129705 q = 1) (hb : d187903 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129705, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42410 q ha hb
    | true =>
      simp only [d129705, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129706 q = 1) (hb : d187904 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129706, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129706, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129735 q = 1) (hb : d187929 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129735, d187929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129735, d187929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129736 q = 1) (hb : d187930 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129736, d187930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129736, d187930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129737 q = 1) (hb : d187931 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129737, d187931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129737, d187931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129738 q = 1) (hb : d187932 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129738, d187932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129738, d187932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42416 (p : Pattern) (ha : d129744 p = 1) (hb : d187938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129705 q = 1) (hb : d187903 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129705, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42410 q ha hb
    | true =>
      simp only [d129705, d187903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129706 q = 1) (hb : d187904 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129706, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129706, d187904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129741 q = 1) (hb : d187935 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129741, d187935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129741, d187935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129742 q = 1) (hb : d187936 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129742, d187936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129742, d187936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129743 q = 1) (hb : d187937 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129743, d187937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129743, d187937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129744 q = 1) (hb : d187938 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129744, d187938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129744, d187938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42417 (p : Pattern) (ha : d129750 p = 1) (hb : d187944 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129739 q = 1) (hb : d187933 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129739, d187933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42415 q ha hb
    | true =>
      simp only [d129739, d187933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42411 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129711 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129740 q = 1) (hb : d187934 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129740, d187934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129740, d187934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129745 q = 1) (hb : d187939 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129745, d187939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42416 q ha hb
    | true =>
      simp only [d129745, d187939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129746 q = 1) (hb : d187940 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129746, d187940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129746, d187940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129747 q = 1) (hb : d187941 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129747, d187941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129747, d187941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129748 q = 1) (hb : d187942 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129748, d187942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129748, d187942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129749 q = 1) (hb : d187943 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129749, d187943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129749, d187943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129750 q = 1) (hb : d187944 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129750, d187944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129750, d187944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro42418 (p : Pattern) (ha : d129756 p = 1) (hb : d187950 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129684 q = 1) (hb : d187886 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129684, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42407 q ha hb
    | true =>
      simp only [d129684, d187886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129752 q = 1) (hb : d187946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129752, d187946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129752, d187946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129753 q = 1) (hb : d187947 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129753, d187947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129753, d187947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129754 q = 1) (hb : d187948 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129754, d187948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129754, d187948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129755 q = 1) (hb : d187949 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129755, d187949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129755, d187949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129756 q = 1) (hb : d187950 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129756, d187950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129756, d187950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42419 (p : Pattern) (ha : d129762 p = 1) (hb : d187956 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129751 q = 1) (hb : d187945 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129751, d187945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129751, d187945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42417 q ha hb
  have h2 (q : Pattern) (ha : d129757 q = 1) (hb : d187951 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129757, d187951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129757, d187951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42418 q ha hb
  have h3 (q : Pattern) (ha : d129758 q = 1) (hb : d187952 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129758, d187952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129758, d187952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129759 q = 1) (hb : d187953 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129759, d187953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129759, d187953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129760 q = 1) (hb : d187954 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129760, d187954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129760, d187954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129761 q = 1) (hb : d187955 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129761, d187955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129761, d187955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129762 q = 1) (hb : d187956 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129762, d187956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129762, d187956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42420 (p : Pattern) (ha : d129768 p = 1) (hb : d187962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129696 q = 1) (hb : d187898 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129696, d187898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129696, d187898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42409 q ha hb
  have h2 (q : Pattern) (ha : d129697 q = 1) (hb : d187899 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129697, d187899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129697, d187899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129698 q = 1) (hb : d187900 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129698, d187900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129698, d187900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129699 q = 1) (hb : d187901 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129699, d187901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129699, d187901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129723 q = 1) (hb : d187921 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129723, d187921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129723, d187921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42413 q ha hb
  have h6 (q : Pattern) (ha : d129724 q = 1) (hb : d187922 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129724, d187922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129724, d187922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129725 q = 1) (hb : d187923 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129725, d187923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129725, d187923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129726 q = 1) (hb : d187924 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129726, d187924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129726, d187924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129727 q = 1) (hb : d187925 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129727, d187925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129727, d187925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d129763 q = 1) (hb : d187957 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129763, d187957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129763, d187957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42419 q ha hb
  have h11 (q : Pattern) (ha : d129764 q = 1) (hb : d187958 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129764, d187958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129764, d187958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d129765 q = 1) (hb : d187959 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129765, d187959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129765, d187959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d129766 q = 1) (hb : d187960 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129766, d187960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129766, d187960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d129767 q = 1) (hb : d187961 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129767, d187961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129767, d187961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d129768 q = 1) (hb : d187962 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129768, d187962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d129768, d187962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro42421 (p : Pattern) (ha : d129775 p = 1) (hb : d187963 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16078 q = 1) (hb : d101090 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16078, d101090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42112 q ha hb
    | true =>
      simp only [d16078, d101090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42101 q ha hb
  have h2 (q : Pattern) (ha : d16079 q = 1) (hb : d129769 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16079, d129769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16079, d129769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16080 q = 1) (hb : d129770 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16080, d129770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16080, d129770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16082 q = 1) (hb : d101094 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16082, d101094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42101 q ha hb
    | true =>
      simp only [d16082, d101094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42113 q ha hb
  have h5 (q : Pattern) (ha : d16083 q = 1) (hb : d129771 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16083, d129771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16083, d129771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16084 q = 1) (hb : d129772 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16084, d129772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16084, d129772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16085 q = 1) (hb : d129773 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16085, d129773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16085, d129773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15967 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42101 q ha hb
    | true =>
      simp only [d15967, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42094 q ha hb
  have h9 (q : Pattern) (ha : d15968 q = 1) (hb : d129728 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d129728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d129728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15969 q = 1) (hb : d129729 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d129729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d129729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d145 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42094 q ha hb
    | true =>
      simp only [d145, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42088 q ha hb
  have h12 (q : Pattern) (ha : d146 q = 1) (hb : d129700 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d129700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d129700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147 q = 1) (hb : d129701 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d129701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d129701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15970 q = 1) (hb : d129730 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d129730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15970, d129730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16086 q = 1) (hb : d129774 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16086, d129774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16086, d129774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18729 q = 1) (hb : d101091 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18729, d101091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18729, d101091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d18730 q = 1) (hb : d101092 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18730, d101092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18730, d101092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d18731 q = 1) (hb : d101095 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18731, d101095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18731, d101095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d18732 q = 1) (hb : d101096 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18732, d101096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18732, d101096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d18733 q = 1) (hb : d101097 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18733, d101097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18733, d101097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d18645 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18645, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18645, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d18646 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18646, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18646, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d18581 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18581, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d18582 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18582, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d18647 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18647, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d18647, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d18734 q = 1) (hb : d101098 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18734, d101098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d18734, d101098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d129775 q = 1) (hb : d187963 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129775, d187963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d129775, d187963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  exact h27 p ha hb
theorem andIntro42422 (p : Pattern) (ha : d129780 p = 1) (hb : d187966 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15967 q = 1) (hb : d101022 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15967, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42101 q ha hb
    | true =>
      simp only [d15967, d101022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42094 q ha hb
  have h2 (q : Pattern) (ha : d15968 q = 1) (hb : d129728 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15968, d129728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15968, d129728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15969 q = 1) (hb : d129729 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15969, d129729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15969, d129729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d145 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42094 q ha hb
    | true =>
      simp only [d145, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42088 q ha hb
  have h5 (q : Pattern) (ha : d146 q = 1) (hb : d129700 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d129700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d129700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147 q = 1) (hb : d129701 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d129701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d129701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15970 q = 1) (hb : d129730 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15970, d129730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15970, d129730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d475 q = 1) (hb : d129778 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d129778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d475, d129778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16035 q = 1) (hb : d129779 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16035, d129779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16035, d129779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18645 q = 1) (hb : d101023 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18645, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18645, d101023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d18646 q = 1) (hb : d101024 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18646, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18646, d101024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18581 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18581, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d18582 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18582, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18647 q = 1) (hb : d101025 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18647, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18647, d101025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18740 q = 1) (hb : d101102 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18740, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18740, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d18741 q = 1) (hb : d101103 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18741, d101103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d18741, d101103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d129780 q = 1) (hb : d187966 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129780, d187966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d129780, d187966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro42423 (p : Pattern) (ha : d129786 p = 1) (hb : d187972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129776 q = 1) (hb : d187964 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129776, d187964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42421 q ha hb
    | true =>
      simp only [d129776, d187964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129777 q = 1) (hb : d187965 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129777, d187965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129777, d187965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129781 q = 1) (hb : d187967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129781, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42422 q ha hb
    | true =>
      simp only [d129781, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129782 q = 1) (hb : d187968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129782, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129782, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129783 q = 1) (hb : d187969 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129783, d187969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129783, d187969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129784 q = 1) (hb : d187970 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129784, d187970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129784, d187970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129785 q = 1) (hb : d187971 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129785, d187971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129785, d187971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129786 q = 1) (hb : d187972 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129786, d187972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129786, d187972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42424 (p : Pattern) (ha : d129788 p = 1) (hb : d187973 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d145 q = 1) (hb : d100981 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d145, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42094 q ha hb
    | true =>
      simp only [d145, d100981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42088 q ha hb
  have h2 (q : Pattern) (ha : d146 q = 1) (hb : d129700 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d146, d129700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d146, d129700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147 q = 1) (hb : d129701 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147, d129701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147, d129701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d475 q = 1) (hb : d129778 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d475, d129778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d475, d129778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d480 q = 1) (hb : d129787 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d480, d129787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d480, d129787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18581 q = 1) (hb : d100982 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18581, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18581, d100982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18582 q = 1) (hb : d100983 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18582, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18582, d100983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18740 q = 1) (hb : d101102 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18740, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18740, d101102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18750 q = 1) (hb : d101111 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18750, d101111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18750, d101111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d129788 q = 1) (hb : d187973 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129788, d187973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d129788, d187973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro42425 (p : Pattern) (ha : d129794 p = 1) (hb : d187979 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129781 q = 1) (hb : d187967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129781, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42422 q ha hb
    | true =>
      simp only [d129781, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129782 q = 1) (hb : d187968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129782, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129782, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129789 q = 1) (hb : d187974 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129789, d187974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42424 q ha hb
    | true =>
      simp only [d129789, d187974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129790 q = 1) (hb : d187975 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129790, d187975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129790, d187975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129791 q = 1) (hb : d187976 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129791, d187976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129791, d187976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129792 q = 1) (hb : d187977 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129792, d187977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129792, d187977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129793 q = 1) (hb : d187978 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129793, d187978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129793, d187978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129794 q = 1) (hb : d187979 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129794, d187979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129794, d187979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42426 (p : Pattern) (ha : d129805 p = 1) (hb : d187985 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129781 q = 1) (hb : d187967 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129781, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42422 q ha hb
    | true =>
      simp only [d129781, d187967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129782 q = 1) (hb : d187968 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129782, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129782, d187968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129802 q = 1) (hb : d187982 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129802, d187982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129802, d187982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129803 q = 1) (hb : d187983 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129803, d187983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129803, d187983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129804 q = 1) (hb : d187984 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129804, d187984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129804, d187984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129805 q = 1) (hb : d187985 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129805, d187985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129805, d187985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42427 (p : Pattern) (ha : d129811 p = 1) (hb : d187991 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129795 q = 1) (hb : d187980 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129795, d187980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42423 q ha hb
    | true =>
      simp only [d129795, d187980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42425 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129800 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129801 q = 1) (hb : d187981 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129801, d187981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129801, d187981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129806 q = 1) (hb : d187986 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129806, d187986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42426 q ha hb
    | true =>
      simp only [d129806, d187986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129807 q = 1) (hb : d187987 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129807, d187987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129807, d187987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129808 q = 1) (hb : d187988 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129808, d187988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129808, d187988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129809 q = 1) (hb : d187989 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129809, d187989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129809, d187989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129810 q = 1) (hb : d187990 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129810, d187990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129810, d187990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129811 q = 1) (hb : d187991 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129811, d187991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129811, d187991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro42428 (p : Pattern) (ha : d129799 p = 1) (hb : d187996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129789 q = 1) (hb : d187974 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129789, d187974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42424 q ha hb
    | true =>
      simp only [d129789, d187974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129790 q = 1) (hb : d187975 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129790, d187975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129790, d187975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129796 q = 1) (hb : d187993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129796, d187993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129796, d187993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129797 q = 1) (hb : d187994 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129797, d187994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129797, d187994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129798 q = 1) (hb : d187995 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129798, d187995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129798, d187995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129799 q = 1) (hb : d187996 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129799, d187996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129799, d187996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42429 (p : Pattern) (ha : d129818 p = 1) (hb : d188002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129813 q = 1) (hb : d187997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129813, d187997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42428 q ha hb
    | true =>
      simp only [d129813, d187997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129814 q = 1) (hb : d187998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129814, d187998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129814, d187998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129815 q = 1) (hb : d187999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129815, d187999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129815, d187999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129816 q = 1) (hb : d188000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129816, d188000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129816, d188000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129817 q = 1) (hb : d188001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129817, d188001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129817, d188001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129818 q = 1) (hb : d188002 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129818, d188002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129818, d188002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42430 (p : Pattern) (ha : d129824 p = 1) (hb : d188008 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129812 q = 1) (hb : d187992 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129812, d187992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129812, d187992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42427 q ha hb
  have h2 (q : Pattern) (ha : d129819 q = 1) (hb : d188003 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129819, d188003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129819, d188003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42429 q ha hb
  have h3 (q : Pattern) (ha : d129820 q = 1) (hb : d188004 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129820, d188004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129820, d188004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129821 q = 1) (hb : d188005 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129821, d188005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129821, d188005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129822 q = 1) (hb : d188006 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129822, d188006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129822, d188006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129823 q = 1) (hb : d188007 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129823, d188007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129823, d188007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129824 q = 1) (hb : d188008 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129824, d188008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129824, d188008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42431 (p : Pattern) (ha : d129830 p = 1) (hb : d188014 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129825 q = 1) (hb : d188009 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129825, d188009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129825, d188009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42430 q ha hb
  have h2 (q : Pattern) (ha : d129826 q = 1) (hb : d188010 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129826, d188010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129826, d188010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129827 q = 1) (hb : d188011 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129827, d188011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129827, d188011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129828 q = 1) (hb : d188012 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129828, d188012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129828, d188012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129829 q = 1) (hb : d188013 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129829, d188013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129829, d188013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129830 q = 1) (hb : d188014 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129830, d188014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129830, d188014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42432 (p : Pattern) (ha : d129843 p = 1) (hb : d188016 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16275 q = 1) (hb : d101189 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16275, d101189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42132 q ha hb
    | true =>
      simp only [d16275, d101189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42131 q ha hb
  have h2 (q : Pattern) (ha : d16276 q = 1) (hb : d129832 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16276, d129832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16276, d129832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16277 q = 1) (hb : d129833 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16277, d129833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16277, d129833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16279 q = 1) (hb : d101194 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16279, d101194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42131 q ha hb
    | true =>
      simp only [d16279, d101194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42133 q ha hb
  have h5 (q : Pattern) (ha : d16280 q = 1) (hb : d129834 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16280, d129834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16280, d129834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16281 q = 1) (hb : d129835 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16281, d129835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16281, d129835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16282 q = 1) (hb : d129836 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16282, d129836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16282, d129836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16228 q = 1) (hb : d101200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42131 q ha hb
    | true =>
      simp only [d16228, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42124 q ha hb
  have h9 (q : Pattern) (ha : d16229 q = 1) (hb : d129837 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16229, d129837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16229, d129837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16230 q = 1) (hb : d129838 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16230, d129838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16230, d129838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d763 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42124 q ha hb
    | true =>
      simp only [d763, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42125 q ha hb
  have h12 (q : Pattern) (ha : d764 q = 1) (hb : d129839 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d129839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d129839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d765 q = 1) (hb : d129840 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d129840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d129840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16231 q = 1) (hb : d129841 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16231, d129841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16231, d129841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16283 q = 1) (hb : d129842 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16283, d129842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16283, d129842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d18868 q = 1) (hb : d101190 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18868, d101190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18868, d101190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d18869 q = 1) (hb : d101191 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18869, d101191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18869, d101191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d18870 q = 1) (hb : d101195 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18870, d101195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18870, d101195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d18871 q = 1) (hb : d101196 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18871, d101196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18871, d101196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d18872 q = 1) (hb : d101197 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18872, d101197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d18872, d101197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d18873 q = 1) (hb : d101201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18873, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18873, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d18874 q = 1) (hb : d101202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18874, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18874, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d18875 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18875, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18875, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d18876 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18876, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18876, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d18877 q = 1) (hb : d101207 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18877, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d18877, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d18878 q = 1) (hb : d101208 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18878, d101208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d18878, d101208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d129843 q = 1) (hb : d188016 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129843, d188016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d129843, d188016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  exact h27 p ha hb
theorem andIntro42433 (p : Pattern) (ha : d129848 p = 1) (hb : d188019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16228 q = 1) (hb : d101200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16228, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42131 q ha hb
    | true =>
      simp only [d16228, d101200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42124 q ha hb
  have h2 (q : Pattern) (ha : d16229 q = 1) (hb : d129837 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16229, d129837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16229, d129837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16230 q = 1) (hb : d129838 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16230, d129838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16230, d129838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d763 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42124 q ha hb
    | true =>
      simp only [d763, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42125 q ha hb
  have h5 (q : Pattern) (ha : d764 q = 1) (hb : d129839 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d129839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d129839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d765 q = 1) (hb : d129840 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d129840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d129840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16231 q = 1) (hb : d129841 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16231, d129841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16231, d129841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d767 q = 1) (hb : d129846 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d129846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d767, d129846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16232 q = 1) (hb : d129847 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16232, d129847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16232, d129847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d18873 q = 1) (hb : d101201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18873, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18873, d101201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d18874 q = 1) (hb : d101202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18874, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18874, d101202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d18875 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18875, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d18875, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d18876 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18876, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18876, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d18877 q = 1) (hb : d101207 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18877, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d18877, d101207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d18884 q = 1) (hb : d101212 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18884, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d18884, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d18885 q = 1) (hb : d101213 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18885, d101213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d18885, d101213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d129848 q = 1) (hb : d188019 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129848, d188019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d129848, d188019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro42434 (p : Pattern) (ha : d129854 p = 1) (hb : d188025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129844 q = 1) (hb : d188017 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129844, d188017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42432 q ha hb
    | true =>
      simp only [d129844, d188017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129845 q = 1) (hb : d188018 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129845, d188018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129845, d188018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129849 q = 1) (hb : d188020 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129849, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42433 q ha hb
    | true =>
      simp only [d129849, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129850 q = 1) (hb : d188021 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129850, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129850, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129851 q = 1) (hb : d188022 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129851, d188022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129851, d188022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129852 q = 1) (hb : d188023 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129852, d188023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129852, d188023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129853 q = 1) (hb : d188024 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129853, d188024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129853, d188024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129854 q = 1) (hb : d188025 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129854, d188025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129854, d188025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42435 (p : Pattern) (ha : d129856 p = 1) (hb : d188026 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d763 q = 1) (hb : d101204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42124 q ha hb
    | true =>
      simp only [d763, d101204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42125 q ha hb
  have h2 (q : Pattern) (ha : d764 q = 1) (hb : d129839 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d129839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d129839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d765 q = 1) (hb : d129840 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d129840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d129840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d767 q = 1) (hb : d129846 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d767, d129846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d767, d129846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d772 q = 1) (hb : d129855 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d772, d129855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d772, d129855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d18875 q = 1) (hb : d101205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d18875, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d18875, d101205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d18876 q = 1) (hb : d101206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d18876, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18876, d101206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d18884 q = 1) (hb : d101212 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d18884, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d18884, d101212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d18894 q = 1) (hb : d101221 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d18894, d101221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d18894, d101221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d129856 q = 1) (hb : d188026 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129856, d188026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d129856, d188026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro42436 (p : Pattern) (ha : d129862 p = 1) (hb : d188032 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129849 q = 1) (hb : d188020 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129849, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42433 q ha hb
    | true =>
      simp only [d129849, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129850 q = 1) (hb : d188021 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129850, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129850, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129857 q = 1) (hb : d188027 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129857, d188027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42435 q ha hb
    | true =>
      simp only [d129857, d188027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129858 q = 1) (hb : d188028 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129858, d188028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129858, d188028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129859 q = 1) (hb : d188029 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129859, d188029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129859, d188029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129860 q = 1) (hb : d188030 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129860, d188030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129860, d188030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129861 q = 1) (hb : d188031 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129861, d188031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129861, d188031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129862 q = 1) (hb : d188032 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129862, d188032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129862, d188032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42437 (p : Pattern) (ha : d129873 p = 1) (hb : d188038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129849 q = 1) (hb : d188020 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129849, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42433 q ha hb
    | true =>
      simp only [d129849, d188020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129850 q = 1) (hb : d188021 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129850, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129850, d188021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129870 q = 1) (hb : d188035 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129870, d188035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129870, d188035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129871 q = 1) (hb : d188036 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129871, d188036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129871, d188036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129872 q = 1) (hb : d188037 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129872, d188037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129872, d188037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129873 q = 1) (hb : d188038 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129873, d188038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129873, d188038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42438 (p : Pattern) (ha : d129879 p = 1) (hb : d188044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129863 q = 1) (hb : d188033 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129863, d188033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42434 q ha hb
    | true =>
      simp only [d129863, d188033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42436 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129868 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129869 q = 1) (hb : d188034 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129869, d188034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129869, d188034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129874 q = 1) (hb : d188039 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129874, d188039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42437 q ha hb
    | true =>
      simp only [d129874, d188039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129875 q = 1) (hb : d188040 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129875, d188040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129875, d188040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129876 q = 1) (hb : d188041 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129876, d188041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129876, d188041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129877 q = 1) (hb : d188042 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129877, d188042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129877, d188042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129878 q = 1) (hb : d188043 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129878, d188043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129878, d188043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129879 q = 1) (hb : d188044 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129879, d188044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129879, d188044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro42439 (p : Pattern) (ha : d129867 p = 1) (hb : d188049 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129857 q = 1) (hb : d188027 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129857, d188027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42435 q ha hb
    | true =>
      simp only [d129857, d188027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129858 q = 1) (hb : d188028 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129858, d188028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129858, d188028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129864 q = 1) (hb : d188046 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129864, d188046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129864, d188046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129865 q = 1) (hb : d188047 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129865, d188047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129865, d188047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129866 q = 1) (hb : d188048 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129866, d188048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129866, d188048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129867 q = 1) (hb : d188049 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129867, d188049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129867, d188049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42440 (p : Pattern) (ha : d129886 p = 1) (hb : d188055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129881 q = 1) (hb : d188050 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129881, d188050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42439 q ha hb
    | true =>
      simp only [d129881, d188050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129882 q = 1) (hb : d188051 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129882, d188051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129882, d188051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129883 q = 1) (hb : d188052 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129883, d188052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129883, d188052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129884 q = 1) (hb : d188053 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129884, d188053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129884, d188053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129885 q = 1) (hb : d188054 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129885, d188054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129885, d188054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129886 q = 1) (hb : d188055 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129886, d188055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129886, d188055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42441 (p : Pattern) (ha : d129892 p = 1) (hb : d188061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129880 q = 1) (hb : d188045 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129880, d188045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129880, d188045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42438 q ha hb
  have h2 (q : Pattern) (ha : d129887 q = 1) (hb : d188056 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129887, d188056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129887, d188056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42440 q ha hb
  have h3 (q : Pattern) (ha : d129888 q = 1) (hb : d188057 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129888, d188057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129888, d188057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129889 q = 1) (hb : d188058 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129889, d188058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129889, d188058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129890 q = 1) (hb : d188059 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129890, d188059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129890, d188059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129891 q = 1) (hb : d188060 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129891, d188060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129891, d188060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129892 q = 1) (hb : d188061 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129892, d188061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129892, d188061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42442 (p : Pattern) (ha : d129898 p = 1) (hb : d188067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129893 q = 1) (hb : d188062 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129893, d188062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129893, d188062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42441 q ha hb
  have h2 (q : Pattern) (ha : d129894 q = 1) (hb : d188063 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129894, d188063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129894, d188063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129895 q = 1) (hb : d188064 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129895, d188064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129895, d188064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129896 q = 1) (hb : d188065 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129896, d188065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129896, d188065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129897 q = 1) (hb : d188066 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129897, d188066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129897, d188066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129898 q = 1) (hb : d188067 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129898, d188067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129898, d188067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42443 (p : Pattern) (ha : d129912 p = 1) (hb : d188070 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16512 q = 1) (hb : d101328 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16512, d101328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42154 q ha hb
    | true =>
      simp only [d16512, d101328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42153 q ha hb
  have h2 (q : Pattern) (ha : d16513 q = 1) (hb : d129901 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16513, d129901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16513, d129901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16514 q = 1) (hb : d129902 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16514, d129902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16514, d129902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16517 q = 1) (hb : d101343 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16517, d101343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42153 q ha hb
    | true =>
      simp only [d16517, d101343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42155 q ha hb
  have h5 (q : Pattern) (ha : d16518 q = 1) (hb : d129903 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16518, d129903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16518, d129903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16519 q = 1) (hb : d129904 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16519, d129904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16519, d129904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16520 q = 1) (hb : d129905 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16520, d129905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16520, d129905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16444 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42153 q ha hb
    | true =>
      simp only [d16444, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42146 q ha hb
  have h9 (q : Pattern) (ha : d16445 q = 1) (hb : d129906 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d129906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d129906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16446 q = 1) (hb : d129907 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d129907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d129907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16447 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42146 q ha hb
    | true =>
      simp only [d16447, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42152 q ha hb
  have h12 (q : Pattern) (ha : d16448 q = 1) (hb : d129908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d129908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d129908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16449 q = 1) (hb : d129909 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d129909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d129909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16450 q = 1) (hb : d129910 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d129910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16450, d129910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16521 q = 1) (hb : d129911 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16521, d129911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16521, d129911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19056 q = 1) (hb : d101329 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19056, d101329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19056, d101329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d19057 q = 1) (hb : d101330 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19057, d101330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19057, d101330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d19058 q = 1) (hb : d101344 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19058, d101344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19058, d101344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d19059 q = 1) (hb : d101345 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19059, d101345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19059, d101345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d19060 q = 1) (hb : d101346 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19060, d101346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19060, d101346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d19061 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19061, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19061, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d19062 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19062, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19062, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d19063 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19063, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19063, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d19064 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19064, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19064, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d19065 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19065, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d19065, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d19066 q = 1) (hb : d101376 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19066, d101376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19066, d101376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d129912 q = 1) (hb : d188070 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129912, d188070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d129912, d188070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  exact h27 p ha hb
theorem andIntro42444 (p : Pattern) (ha : d129917 p = 1) (hb : d188073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42153 q ha hb
    | true =>
      simp only [d16444, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42146 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d129906 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d129906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d129906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d129907 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d129907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d129907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42146 q ha hb
    | true =>
      simp only [d16447, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42152 q ha hb
  have h5 (q : Pattern) (ha : d16448 q = 1) (hb : d129908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d129908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d129908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16449 q = 1) (hb : d129909 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d129909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d129909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16450 q = 1) (hb : d129910 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d129910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d129910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16525 q = 1) (hb : d129915 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16525, d129915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16525, d129915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16526 q = 1) (hb : d129916 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16526, d129916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16526, d129916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19061 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19061, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19061, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d19062 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19062, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19062, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19063 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19063, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19063, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d19064 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19064, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19064, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19065 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19065, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19065, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19072 q = 1) (hb : d101380 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19072, d101380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19072, d101380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d19073 q = 1) (hb : d101381 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19073, d101381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19073, d101381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d129917 q = 1) (hb : d188073 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129917, d188073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d129917, d188073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro42445 (p : Pattern) (ha : d129923 p = 1) (hb : d188079 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129913 q = 1) (hb : d188071 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129913, d188071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42443 q ha hb
    | true =>
      simp only [d129913, d188071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129914 q = 1) (hb : d188072 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129914, d188072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129914, d188072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129918 q = 1) (hb : d188074 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129918, d188074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42444 q ha hb
    | true =>
      simp only [d129918, d188074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129919 q = 1) (hb : d188075 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129919, d188075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129919, d188075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129920 q = 1) (hb : d188076 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129920, d188076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129920, d188076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129921 q = 1) (hb : d188077 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129921, d188077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129921, d188077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129922 q = 1) (hb : d188078 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129922, d188078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129922, d188078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129923 q = 1) (hb : d188079 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129923, d188079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129923, d188079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42446 (p : Pattern) (ha : d129928 p = 1) (hb : d188080 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16451 q = 1) (hb : d101391 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16451, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42146 q ha hb
    | true =>
      simp only [d16451, d101391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42145 q ha hb
  have h2 (q : Pattern) (ha : d16452 q = 1) (hb : d129924 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16452, d129924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16452, d129924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16453 q = 1) (hb : d129925 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16453, d129925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16453, d129925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16454 q = 1) (hb : d129926 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16454, d129926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16454, d129926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16459 q = 1) (hb : d129927 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16459, d129927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16459, d129927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19088 q = 1) (hb : d101392 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19088, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19088, d101392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19089 q = 1) (hb : d101393 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19089, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19089, d101393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19090 q = 1) (hb : d101394 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19090, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19090, d101394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19091 q = 1) (hb : d101395 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19091, d101395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19091, d101395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d129928 q = 1) (hb : d188080 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129928, d188080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d129928, d188080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro42447 (p : Pattern) (ha : d129934 p = 1) (hb : d188086 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129918 q = 1) (hb : d188074 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129918, d188074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42444 q ha hb
    | true =>
      simp only [d129918, d188074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129919 q = 1) (hb : d188075 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129919, d188075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129919, d188075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129929 q = 1) (hb : d188081 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129929, d188081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42446 q ha hb
    | true =>
      simp only [d129929, d188081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129930 q = 1) (hb : d188082 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129930, d188082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129930, d188082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129931 q = 1) (hb : d188083 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129931, d188083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129931, d188083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129932 q = 1) (hb : d188084 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129932, d188084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129932, d188084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129933 q = 1) (hb : d188085 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129933, d188085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d129933, d188085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d129934 q = 1) (hb : d188086 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129934, d188086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d129934, d188086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42448 (p : Pattern) (ha : d129954 p = 1) (hb : d188089 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16444 q = 1) (hb : d101355 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16444, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42153 q ha hb
    | true =>
      simp only [d16444, d101355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42146 q ha hb
  have h2 (q : Pattern) (ha : d16445 q = 1) (hb : d129906 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16445, d129906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16445, d129906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16446 q = 1) (hb : d129907 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16446, d129907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16446, d129907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16447 q = 1) (hb : d101372 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16447, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42146 q ha hb
    | true =>
      simp only [d16447, d101372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42152 q ha hb
  have h5 (q : Pattern) (ha : d16448 q = 1) (hb : d129908 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16448, d129908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16448, d129908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16449 q = 1) (hb : d129909 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16449, d129909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16449, d129909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16450 q = 1) (hb : d129910 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16450, d129910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16450, d129910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16574 q = 1) (hb : d101419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16574, d101419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42146 q ha hb
    | true =>
      simp only [d16574, d101419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42164 q ha hb
  have h9 (q : Pattern) (ha : d16575 q = 1) (hb : d129950 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16575, d129950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16575, d129950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16576 q = 1) (hb : d129951 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16576, d129951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16576, d129951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16577 q = 1) (hb : d129952 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16577, d129952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16577, d129952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16578 q = 1) (hb : d129953 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16578, d129953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16578, d129953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19061 q = 1) (hb : d101356 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19061, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19061, d101356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d19062 q = 1) (hb : d101357 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19062, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19062, d101357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19063 q = 1) (hb : d101373 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19063, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19063, d101373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d19064 q = 1) (hb : d101374 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19064, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19064, d101374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19065 q = 1) (hb : d101375 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19065, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19065, d101375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d19180 q = 1) (hb : d101420 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19180, d101420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19180, d101420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d19181 q = 1) (hb : d101421 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19181, d101421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19181, d101421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d19182 q = 1) (hb : d101422 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19182, d101422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d19182, d101422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d19183 q = 1) (hb : d101423 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19183, d101423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19183, d101423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d129954 q = 1) (hb : d188089 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d129954, d188089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d129954, d188089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  exact h22 p ha hb
theorem andIntro42449 (p : Pattern) (ha : d129960 p = 1) (hb : d188095 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129955 q = 1) (hb : d188090 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129955, d188090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42448 q ha hb
    | true =>
      simp only [d129955, d188090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129956 q = 1) (hb : d188091 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129956, d188091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129956, d188091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129957 q = 1) (hb : d188092 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129957, d188092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129957, d188092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129958 q = 1) (hb : d188093 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129958, d188093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129958, d188093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129959 q = 1) (hb : d188094 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129959, d188094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129959, d188094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129960 q = 1) (hb : d188095 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129960, d188095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129960, d188095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42450 (p : Pattern) (ha : d129966 p = 1) (hb : d188101 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129935 q = 1) (hb : d188087 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129935, d188087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42445 q ha hb
    | true =>
      simp only [d129935, d188087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42447 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d129948 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d129949 q = 1) (hb : d188088 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129949, d188088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129949, d188088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d129961 q = 1) (hb : d188096 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129961, d188096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42449 q ha hb
    | true =>
      simp only [d129961, d188096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129962 q = 1) (hb : d188097 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129962, d188097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129962, d188097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129963 q = 1) (hb : d188098 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129963, d188098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129963, d188098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d129964 q = 1) (hb : d188099 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129964, d188099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129964, d188099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d129965 q = 1) (hb : d188100 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129965, d188100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129965, d188100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d129966 q = 1) (hb : d188101 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129966, d188101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129966, d188101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro42451 (p : Pattern) (ha : d129947 p = 1) (hb : d188106 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129929 q = 1) (hb : d188081 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d129929, d188081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42446 q ha hb
    | true =>
      simp only [d129929, d188081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129930 q = 1) (hb : d188082 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d129930, d188082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129930, d188082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129944 q = 1) (hb : d188103 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d129944, d188103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129944, d188103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129945 q = 1) (hb : d188104 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d129945, d188104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129945, d188104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129946 q = 1) (hb : d188105 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d129946, d188105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129946, d188105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129947 q = 1) (hb : d188106 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d129947, d188106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129947, d188106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42452 (p : Pattern) (ha : d129973 p = 1) (hb : d188112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129968 q = 1) (hb : d188107 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d129968, d188107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42451 q ha hb
    | true =>
      simp only [d129968, d188107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d129969 q = 1) (hb : d188108 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d129969, d188108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129969, d188108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129970 q = 1) (hb : d188109 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d129970, d188109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d129970, d188109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d129971 q = 1) (hb : d188110 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d129971, d188110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129971, d188110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129972 q = 1) (hb : d188111 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d129972, d188111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129972, d188111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129973 q = 1) (hb : d188112 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d129973, d188112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129973, d188112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42453 (p : Pattern) (ha : d129979 p = 1) (hb : d188118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129967 q = 1) (hb : d188102 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129967, d188102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129967, d188102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42450 q ha hb
  have h2 (q : Pattern) (ha : d129974 q = 1) (hb : d188113 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d129974, d188113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129974, d188113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42452 q ha hb
  have h3 (q : Pattern) (ha : d129975 q = 1) (hb : d188114 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d129975, d188114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d129975, d188114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129976 q = 1) (hb : d188115 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d129976, d188115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129976, d188115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d129977 q = 1) (hb : d188116 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d129977, d188116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d129977, d188116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d129978 q = 1) (hb : d188117 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d129978, d188117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d129978, d188117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d129979 q = 1) (hb : d188118 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d129979, d188118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129979, d188118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42454 (p : Pattern) (ha : d129985 p = 1) (hb : d188124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d129980 q = 1) (hb : d188119 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d129980, d188119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129980, d188119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42453 q ha hb
  have h2 (q : Pattern) (ha : d129981 q = 1) (hb : d188120 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d129981, d188120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129981, d188120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d129982 q = 1) (hb : d188121 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d129982, d188121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129982, d188121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129983 q = 1) (hb : d188122 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d129983, d188122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129983, d188122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d129984 q = 1) (hb : d188123 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d129984, d188123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129984, d188123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129985 q = 1) (hb : d188124 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d129985, d188124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d129985, d188124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42455 (p : Pattern) (ha : d130000 p = 1) (hb : d188128 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16864 q = 1) (hb : d101519 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16864, d101519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42180 q ha hb
    | true =>
      simp only [d16864, d101519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42179 q ha hb
  have h2 (q : Pattern) (ha : d16865 q = 1) (hb : d129989 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16865, d129989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16865, d129989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16866 q = 1) (hb : d129990 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16866, d129990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16866, d129990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16869 q = 1) (hb : d101534 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16869, d101534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42179 q ha hb
    | true =>
      simp only [d16869, d101534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42181 q ha hb
  have h5 (q : Pattern) (ha : d16870 q = 1) (hb : d129991 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16870, d129991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16870, d129991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16871 q = 1) (hb : d129992 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16871, d129992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16871, d129992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16872 q = 1) (hb : d129993 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16872, d129993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16872, d129993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16796 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42179 q ha hb
    | true =>
      simp only [d16796, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42172 q ha hb
  have h9 (q : Pattern) (ha : d16797 q = 1) (hb : d129994 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d129994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d129994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16798 q = 1) (hb : d129995 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d129995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d129995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16799 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42172 q ha hb
    | true =>
      simp only [d16799, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42178 q ha hb
  have h12 (q : Pattern) (ha : d16800 q = 1) (hb : d129996 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d129996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d129996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d16801 q = 1) (hb : d129997 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d129997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d129997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d16802 q = 1) (hb : d129998 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d129998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16802, d129998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d16873 q = 1) (hb : d129999 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16873, d129999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16873, d129999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19288 q = 1) (hb : d101520 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19288, d101520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19288, d101520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d19289 q = 1) (hb : d101521 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19289, d101521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19289, d101521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d19290 q = 1) (hb : d101535 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19290, d101535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19290, d101535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d19291 q = 1) (hb : d101536 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19291, d101536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19291, d101536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d19292 q = 1) (hb : d101537 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19292, d101537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19292, d101537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d19293 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19293, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19293, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d19294 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19294, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19294, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d19295 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19295, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19295, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d19296 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19296, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19296, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d19297 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19297, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d19297, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d19298 q = 1) (hb : d101573 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19298, d101573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19298, d101573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d130000 q = 1) (hb : d188128 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130000, d188128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d130000, d188128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  exact h27 p ha hb
theorem andIntro42456 (p : Pattern) (ha : d130005 p = 1) (hb : d188131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42179 q ha hb
    | true =>
      simp only [d16796, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42172 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d129994 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d129994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d129994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d129995 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d129995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d129995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16799 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42172 q ha hb
    | true =>
      simp only [d16799, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42178 q ha hb
  have h5 (q : Pattern) (ha : d16800 q = 1) (hb : d129996 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d129996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d129996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16801 q = 1) (hb : d129997 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d129997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d129997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16802 q = 1) (hb : d129998 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d129998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d129998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16877 q = 1) (hb : d130003 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16877, d130003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d16877, d130003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d16878 q = 1) (hb : d130004 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16878, d130004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16878, d130004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19293 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19293, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19293, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d19294 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19294, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19294, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19295 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19295, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19295, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d19296 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19296, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19296, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19297 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19297, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19297, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19304 q = 1) (hb : d101577 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19304, d101577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19304, d101577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d19305 q = 1) (hb : d101578 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19305, d101578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19305, d101578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d130005 q = 1) (hb : d188131 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130005, d188131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d130005, d188131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro42457 (p : Pattern) (ha : d130011 p = 1) (hb : d188137 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130001 q = 1) (hb : d188129 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130001, d188129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42455 q ha hb
    | true =>
      simp only [d130001, d188129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130002 q = 1) (hb : d188130 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130002, d188130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130002, d188130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130006 q = 1) (hb : d188132 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130006, d188132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42456 q ha hb
    | true =>
      simp only [d130006, d188132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130007 q = 1) (hb : d188133 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130007, d188133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130007, d188133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130008 q = 1) (hb : d188134 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130008, d188134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130008, d188134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130009 q = 1) (hb : d188135 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130009, d188135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130009, d188135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130010 q = 1) (hb : d188136 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130010, d188136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130010, d188136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130011 q = 1) (hb : d188137 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130011, d188137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130011, d188137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42458 (p : Pattern) (ha : d130016 p = 1) (hb : d188138 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16803 q = 1) (hb : d101591 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16803, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42172 q ha hb
    | true =>
      simp only [d16803, d101591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42171 q ha hb
  have h2 (q : Pattern) (ha : d16804 q = 1) (hb : d130012 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16804, d130012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16804, d130012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16805 q = 1) (hb : d130013 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16805, d130013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16805, d130013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16806 q = 1) (hb : d130014 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16806, d130014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16806, d130014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d16811 q = 1) (hb : d130015 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16811, d130015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d16811, d130015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19323 q = 1) (hb : d101592 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19323, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19323, d101592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19324 q = 1) (hb : d101593 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19324, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19324, d101593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19325 q = 1) (hb : d101594 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19325, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19325, d101594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19326 q = 1) (hb : d101595 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19326, d101595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19326, d101595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d130016 q = 1) (hb : d188138 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130016, d188138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d130016, d188138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro42459 (p : Pattern) (ha : d130022 p = 1) (hb : d188144 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130006 q = 1) (hb : d188132 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130006, d188132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42456 q ha hb
    | true =>
      simp only [d130006, d188132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130007 q = 1) (hb : d188133 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130007, d188133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130007, d188133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130017 q = 1) (hb : d188139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130017, d188139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42458 q ha hb
    | true =>
      simp only [d130017, d188139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130018 q = 1) (hb : d188140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130018, d188140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130018, d188140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130019 q = 1) (hb : d188141 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130019, d188141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130019, d188141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130020 q = 1) (hb : d188142 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130020, d188142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130020, d188142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130021 q = 1) (hb : d188143 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130021, d188143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130021, d188143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130022 q = 1) (hb : d188144 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130022, d188144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130022, d188144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42460 (p : Pattern) (ha : d130042 p = 1) (hb : d188147 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d16796 q = 1) (hb : d101549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16796, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42179 q ha hb
    | true =>
      simp only [d16796, d101549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42172 q ha hb
  have h2 (q : Pattern) (ha : d16797 q = 1) (hb : d129994 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16797, d129994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16797, d129994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d16798 q = 1) (hb : d129995 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16798, d129995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16798, d129995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16799 q = 1) (hb : d101569 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16799, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42172 q ha hb
    | true =>
      simp only [d16799, d101569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42178 q ha hb
  have h5 (q : Pattern) (ha : d16800 q = 1) (hb : d129996 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16800, d129996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16800, d129996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d16801 q = 1) (hb : d129997 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16801, d129997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16801, d129997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d16802 q = 1) (hb : d129998 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16802, d129998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16802, d129998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d16929 q = 1) (hb : d101619 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d16929, d101619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42172 q ha hb
    | true =>
      simp only [d16929, d101619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42190 q ha hb
  have h9 (q : Pattern) (ha : d16930 q = 1) (hb : d130038 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d16930, d130038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16930, d130038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d16931 q = 1) (hb : d130039 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d16931, d130039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16931, d130039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d16932 q = 1) (hb : d130040 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d16932, d130040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d16932, d130040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d16933 q = 1) (hb : d130041 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d16933, d130041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d16933, d130041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19293 q = 1) (hb : d101550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19293, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19293, d101550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d19294 q = 1) (hb : d101551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19294, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19294, d101551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19295 q = 1) (hb : d101570 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19295, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19295, d101570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d19296 q = 1) (hb : d101571 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19296, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19296, d101571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19297 q = 1) (hb : d101572 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19297, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19297, d101572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d19418 q = 1) (hb : d101620 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19418, d101620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19418, d101620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d19419 q = 1) (hb : d101621 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19419, d101621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19419, d101621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d19420 q = 1) (hb : d101622 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19420, d101622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d19420, d101622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d19421 q = 1) (hb : d101623 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19421, d101623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19421, d101623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d130042 q = 1) (hb : d188147 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130042, d188147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d130042, d188147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  exact h22 p ha hb
theorem andIntro42461 (p : Pattern) (ha : d130048 p = 1) (hb : d188153 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130043 q = 1) (hb : d188148 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130043, d188148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42460 q ha hb
    | true =>
      simp only [d130043, d188148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130044 q = 1) (hb : d188149 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130044, d188149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130044, d188149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130045 q = 1) (hb : d188150 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130045, d188150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130045, d188150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130046 q = 1) (hb : d188151 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130046, d188151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130046, d188151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130047 q = 1) (hb : d188152 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130047, d188152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130047, d188152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130048 q = 1) (hb : d188153 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130048, d188153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130048, d188153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42462 (p : Pattern) (ha : d130054 p = 1) (hb : d188159 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130023 q = 1) (hb : d188145 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130023, d188145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42457 q ha hb
    | true =>
      simp only [d130023, d188145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42459 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130036 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130037 q = 1) (hb : d188146 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130037, d188146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130037, d188146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130049 q = 1) (hb : d188154 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130049, d188154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42461 q ha hb
    | true =>
      simp only [d130049, d188154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130050 q = 1) (hb : d188155 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130050, d188155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130050, d188155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130051 q = 1) (hb : d188156 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130051, d188156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130051, d188156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130052 q = 1) (hb : d188157 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130052, d188157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130052, d188157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130053 q = 1) (hb : d188158 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130053, d188158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130053, d188158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130054 q = 1) (hb : d188159 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130054, d188159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130054, d188159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro42463 (p : Pattern) (ha : d130035 p = 1) (hb : d188164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130017 q = 1) (hb : d188139 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130017, d188139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42458 q ha hb
    | true =>
      simp only [d130017, d188139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130018 q = 1) (hb : d188140 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130018, d188140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130018, d188140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130032 q = 1) (hb : d188161 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130032, d188161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130032, d188161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130033 q = 1) (hb : d188162 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130033, d188162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130033, d188162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130034 q = 1) (hb : d188163 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130034, d188163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130034, d188163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130035 q = 1) (hb : d188164 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130035, d188164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130035, d188164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42464 (p : Pattern) (ha : d130061 p = 1) (hb : d188170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130056 q = 1) (hb : d188165 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130056, d188165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42463 q ha hb
    | true =>
      simp only [d130056, d188165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130057 q = 1) (hb : d188166 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130057, d188166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130057, d188166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130058 q = 1) (hb : d188167 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130058, d188167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130058, d188167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130059 q = 1) (hb : d188168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130059, d188168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130059, d188168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130060 q = 1) (hb : d188169 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130060, d188169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130060, d188169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130061 q = 1) (hb : d188170 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130061, d188170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130061, d188170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42465 (p : Pattern) (ha : d130067 p = 1) (hb : d188176 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130055 q = 1) (hb : d188160 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130055, d188160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130055, d188160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42462 q ha hb
  have h2 (q : Pattern) (ha : d130062 q = 1) (hb : d188171 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130062, d188171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130062, d188171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42464 q ha hb
  have h3 (q : Pattern) (ha : d130063 q = 1) (hb : d188172 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130063, d188172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130063, d188172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130064 q = 1) (hb : d188173 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130064, d188173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130064, d188173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130065 q = 1) (hb : d188174 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130065, d188174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130065, d188174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130066 q = 1) (hb : d188175 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130066, d188175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130066, d188175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130067 q = 1) (hb : d188176 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130067, d188176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130067, d188176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42466 (p : Pattern) (ha : d130073 p = 1) (hb : d188182 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130068 q = 1) (hb : d188177 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130068, d188177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130068, d188177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42465 q ha hb
  have h2 (q : Pattern) (ha : d130069 q = 1) (hb : d188178 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130069, d188178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130069, d188178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130070 q = 1) (hb : d188179 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130070, d188179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130070, d188179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130071 q = 1) (hb : d188180 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130071, d188180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130071, d188180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130072 q = 1) (hb : d188181 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130072, d188181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130072, d188181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130073 q = 1) (hb : d188182 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130073, d188182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130073, d188182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42467 (p : Pattern) (ha : d130089 p = 1) (hb : d188187 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17230 q = 1) (hb : d101699 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17230, d101699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42206 q ha hb
    | true =>
      simp only [d17230, d101699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42205 q ha hb
  have h2 (q : Pattern) (ha : d17231 q = 1) (hb : d130078 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17231, d130078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17231, d130078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17232 q = 1) (hb : d130079 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17232, d130079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17232, d130079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17234 q = 1) (hb : d101704 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17234, d101704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42205 q ha hb
    | true =>
      simp only [d17234, d101704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42207 q ha hb
  have h5 (q : Pattern) (ha : d17235 q = 1) (hb : d130080 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17235, d130080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17235, d130080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17236 q = 1) (hb : d130081 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17236, d130081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17236, d130081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17237 q = 1) (hb : d130082 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17237, d130082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17237, d130082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17162 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42205 q ha hb
    | true =>
      simp only [d17162, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
  have h9 (q : Pattern) (ha : d17163 q = 1) (hb : d130083 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d130083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d130083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17164 q = 1) (hb : d130084 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d130084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d130084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17165 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
    | true =>
      simp only [d17165, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42204 q ha hb
  have h12 (q : Pattern) (ha : d17166 q = 1) (hb : d130085 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d130085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d130085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d17167 q = 1) (hb : d130086 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d130086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d130086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d17168 q = 1) (hb : d130087 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d130087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17168, d130087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d17238 q = 1) (hb : d130088 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17238, d130088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17238, d130088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d19520 q = 1) (hb : d101700 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19520, d101700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19520, d101700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h17 (q : Pattern) (ha : d19521 q = 1) (hb : d101701 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19521, d101701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19521, d101701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d19522 q = 1) (hb : d101705 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19522, d101705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19522, d101705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d19523 q = 1) (hb : d101706 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19523, d101706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19523, d101706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d19524 q = 1) (hb : d101707 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19524, d101707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19524, d101707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d19525 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19525, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19525, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d19526 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19526, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19526, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
  have h23 (q : Pattern) (ha : d19527 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19527, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19527, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d19528 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19528, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19528, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
  have h25 (q : Pattern) (ha : d19529 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19529, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d19529, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
  have h26 (q : Pattern) (ha : d19530 q = 1) (hb : d101744 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19530, d101744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d19530, d101744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d130089 q = 1) (hb : d188187 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130089, d188187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
    | true =>
      simp only [d130089, d188187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q hb ha
  exact h27 p ha hb
theorem andIntro42468 (p : Pattern) (ha : d130094 p = 1) (hb : d188190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42205 q ha hb
    | true =>
      simp only [d17162, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
  have h2 (q : Pattern) (ha : d17163 q = 1) (hb : d130083 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d130083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d130083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17164 q = 1) (hb : d130084 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d130084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d130084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17165 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
    | true =>
      simp only [d17165, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42204 q ha hb
  have h5 (q : Pattern) (ha : d17166 q = 1) (hb : d130085 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d130085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d130085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17167 q = 1) (hb : d130086 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d130086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d130086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17168 q = 1) (hb : d130087 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d130087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17168, d130087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17242 q = 1) (hb : d130092 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17242, d130092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d17242, d130092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d17243 q = 1) (hb : d130093 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17243, d130093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17243, d130093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19525 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19525, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19525, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d19526 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19526, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19526, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d19527 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19527, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19527, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d19528 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19528, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19528, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d19529 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19529, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d19529, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19536 q = 1) (hb : d101748 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19536, d101748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d19536, d101748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d19537 q = 1) (hb : d101749 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19537, d101749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19537, d101749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d130094 q = 1) (hb : d188190 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130094, d188190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d130094, d188190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro42469 (p : Pattern) (ha : d130100 p = 1) (hb : d188196 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130090 q = 1) (hb : d188188 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130090, d188188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42467 q ha hb
    | true =>
      simp only [d130090, d188188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130091 q = 1) (hb : d188189 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130091, d188189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130091, d188189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130095 q = 1) (hb : d188191 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130095, d188191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42468 q ha hb
    | true =>
      simp only [d130095, d188191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130096 q = 1) (hb : d188192 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130096, d188192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130096, d188192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130097 q = 1) (hb : d188193 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130097, d188193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130097, d188193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130098 q = 1) (hb : d188194 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130098, d188194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130098, d188194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130099 q = 1) (hb : d188195 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130099, d188195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130099, d188195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130100 q = 1) (hb : d188196 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130100, d188196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130100, d188196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42470 (p : Pattern) (ha : d130105 p = 1) (hb : d188197 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17169 q = 1) (hb : d101762 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17169, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
    | true =>
      simp only [d17169, d101762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42197 q ha hb
  have h2 (q : Pattern) (ha : d17170 q = 1) (hb : d130101 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17170, d130101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17170, d130101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17171 q = 1) (hb : d130102 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17171, d130102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17171, d130102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17172 q = 1) (hb : d130103 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17172, d130103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17172, d130103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17177 q = 1) (hb : d130104 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17177, d130104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d17177, d130104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d19555 q = 1) (hb : d101763 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19555, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19555, d101763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d19556 q = 1) (hb : d101764 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19556, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19556, d101764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19557 q = 1) (hb : d101765 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19557, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d19557, d101765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d19558 q = 1) (hb : d101766 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19558, d101766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19558, d101766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d130105 q = 1) (hb : d188197 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130105, d188197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d130105, d188197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro42471 (p : Pattern) (ha : d130111 p = 1) (hb : d188203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130095 q = 1) (hb : d188191 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130095, d188191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42468 q ha hb
    | true =>
      simp only [d130095, d188191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130096 q = 1) (hb : d188192 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130096, d188192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130096, d188192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130106 q = 1) (hb : d188198 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130106, d188198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42470 q ha hb
    | true =>
      simp only [d130106, d188198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130107 q = 1) (hb : d188199 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130107, d188199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130107, d188199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130108 q = 1) (hb : d188200 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130108, d188200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130108, d188200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130109 q = 1) (hb : d188201 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130109, d188201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130109, d188201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130110 q = 1) (hb : d188202 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130110, d188202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130110, d188202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d130111 q = 1) (hb : d188203 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130111, d188203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d130111, d188203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42472 (p : Pattern) (ha : d130131 p = 1) (hb : d188206 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17162 q = 1) (hb : d101719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17162, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42205 q ha hb
    | true =>
      simp only [d17162, d101719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
  have h2 (q : Pattern) (ha : d17163 q = 1) (hb : d130083 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17163, d130083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17163, d130083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d17164 q = 1) (hb : d130084 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17164, d130084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17164, d130084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17165 q = 1) (hb : d101740 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17165, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
    | true =>
      simp only [d17165, d101740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42204 q ha hb
  have h5 (q : Pattern) (ha : d17166 q = 1) (hb : d130085 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17166, d130085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17166, d130085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17167 q = 1) (hb : d130086 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17167, d130086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17167, d130086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d17168 q = 1) (hb : d130087 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17168, d130087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17168, d130087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d17294 q = 1) (hb : d101790 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d17294, d101790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42198 q ha hb
    | true =>
      simp only [d17294, d101790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42216 q ha hb
  have h9 (q : Pattern) (ha : d17295 q = 1) (hb : d130127 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d17295, d130127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17295, d130127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d17296 q = 1) (hb : d130128 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d17296, d130128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17296, d130128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d17297 q = 1) (hb : d130129 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d17297, d130129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d17297, d130129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d17298 q = 1) (hb : d130130 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d17298, d130130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d17298, d130130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d19525 q = 1) (hb : d101720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19525, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d19525, d101720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d19526 q = 1) (hb : d101721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19526, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19526, d101721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d19527 q = 1) (hb : d101741 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19527, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d19527, d101741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d19528 q = 1) (hb : d101742 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19528, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19528, d101742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d19529 q = 1) (hb : d101743 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19529, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d19529, d101743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d19650 q = 1) (hb : d101791 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19650, d101791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d19650, d101791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d19651 q = 1) (hb : d101792 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19651, d101792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19651, d101792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d19652 q = 1) (hb : d101793 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19652, d101793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d19652, d101793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d19653 q = 1) (hb : d101794 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d19653, d101794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d19653, d101794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d130131 q = 1) (hb : d188206 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d130131, d188206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d130131, d188206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q hb ha
  exact h22 p ha hb
theorem andIntro42473 (p : Pattern) (ha : d130137 p = 1) (hb : d188212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130132 q = 1) (hb : d188207 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130132, d188207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42472 q ha hb
    | true =>
      simp only [d130132, d188207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130133 q = 1) (hb : d188208 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130133, d188208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130133, d188208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130134 q = 1) (hb : d188209 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130134, d188209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130134, d188209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130135 q = 1) (hb : d188210 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130135, d188210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130135, d188210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130136 q = 1) (hb : d188211 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130136, d188211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130136, d188211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130137 q = 1) (hb : d188212 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130137, d188212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130137, d188212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42474 (p : Pattern) (ha : d130143 p = 1) (hb : d188218 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130112 q = 1) (hb : d188204 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130112, d188204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42469 q ha hb
    | true =>
      simp only [d130112, d188204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42471 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d130125 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d130126 q = 1) (hb : d188205 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130126, d188205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130126, d188205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d130138 q = 1) (hb : d188213 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130138, d188213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42473 q ha hb
    | true =>
      simp only [d130138, d188213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130139 q = 1) (hb : d188214 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130139, d188214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130139, d188214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130140 q = 1) (hb : d188215 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130140, d188215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130140, d188215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130141 q = 1) (hb : d188216 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130141, d188216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130141, d188216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d130142 q = 1) (hb : d188217 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130142, d188217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130142, d188217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130143 q = 1) (hb : d188218 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130143, d188218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130143, d188218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro42475 (p : Pattern) (ha : d130124 p = 1) (hb : d188223 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130106 q = 1) (hb : d188198 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d130106, d188198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42470 q ha hb
    | true =>
      simp only [d130106, d188198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130107 q = 1) (hb : d188199 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d130107, d188199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130107, d188199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130121 q = 1) (hb : d188220 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d130121, d188220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130121, d188220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130122 q = 1) (hb : d188221 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d130122, d188221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130122, d188221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130123 q = 1) (hb : d188222 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d130123, d188222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130123, d188222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130124 q = 1) (hb : d188223 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d130124, d188223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130124, d188223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42476 (p : Pattern) (ha : d130150 p = 1) (hb : d188229 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130145 q = 1) (hb : d188224 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d130145, d188224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42475 q ha hb
    | true =>
      simp only [d130145, d188224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130146 q = 1) (hb : d188225 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d130146, d188225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130146, d188225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130147 q = 1) (hb : d188226 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d130147, d188226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130147, d188226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130148 q = 1) (hb : d188227 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d130148, d188227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130148, d188227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130149 q = 1) (hb : d188228 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d130149, d188228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130149, d188228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130150 q = 1) (hb : d188229 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d130150, d188229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130150, d188229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42477 (p : Pattern) (ha : d130156 p = 1) (hb : d188235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130144 q = 1) (hb : d188219 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130144, d188219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130144, d188219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42474 q ha hb
  have h2 (q : Pattern) (ha : d130151 q = 1) (hb : d188230 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d130151, d188230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130151, d188230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42476 q ha hb
  have h3 (q : Pattern) (ha : d130152 q = 1) (hb : d188231 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d130152, d188231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130152, d188231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130153 q = 1) (hb : d188232 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d130153, d188232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130153, d188232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130154 q = 1) (hb : d188233 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d130154, d188233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130154, d188233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130155 q = 1) (hb : d188234 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d130155, d188234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130155, d188234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d130156 q = 1) (hb : d188235 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d130156, d188235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130156, d188235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro42478 (p : Pattern) (ha : d130162 p = 1) (hb : d188241 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130157 q = 1) (hb : d188236 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d130157, d188236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130157, d188236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42477 q ha hb
  have h2 (q : Pattern) (ha : d130158 q = 1) (hb : d188237 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d130158, d188237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130158, d188237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d130159 q = 1) (hb : d188238 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d130159, d188238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130159, d188238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d130160 q = 1) (hb : d188239 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d130160, d188239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130160, d188239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d130161 q = 1) (hb : d188240 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d130161, d188240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130161, d188240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d130162 q = 1) (hb : d188241 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d130162, d188241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d130162, d188241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42479 (p : Pattern) (ha : d130168 p = 1) (hb : d188247 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d129831 q = 1) (hb : d188015 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129831, d188015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42420 q ha hb
    | true =>
      simp only [d129831, d188015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42431 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d129899 q = 1) (hb : d188068 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129899, d188068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129899, d188068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42442 q ha hb
  have h3 (q : Pattern) (ha : d129900 q = 1) (hb : d188069 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129900, d188069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d129900, d188069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d129986 q = 1) (hb : d188125 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d129986, d188125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129986, d188125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42454 q ha hb
  have h5 (q : Pattern) (ha : d129987 q = 1) (hb : d188126 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d129987, d188126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d129987, d188126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d129988 q = 1) (hb : d188127 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d129988, d188127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d129988, d188127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d130074 q = 1) (hb : d188183 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130074, d188183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130074, d188183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42466 q ha hb
  have h8 (q : Pattern) (ha : d130075 q = 1) (hb : d188184 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130075, d188184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130075, d188184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d130076 q = 1) (hb : d188185 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130076, d188185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130076, d188185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d130077 q = 1) (hb : d188186 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130077, d188186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d130077, d188186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d130163 q = 1) (hb : d188242 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d130163, d188242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130163, d188242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42478 q ha hb
  have h12 (q : Pattern) (ha : d130164 q = 1) (hb : d188243 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d130164, d188243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130164, d188243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d130165 q = 1) (hb : d188244 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d130165, d188244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130165, d188244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d130166 q = 1) (hb : d188245 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d130166, d188245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d130166, d188245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d130167 q = 1) (hb : d188246 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d130167, d188246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d130167, d188246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d130168 q = 1) (hb : d188247 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d130168, d188247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d130168, d188247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro42480 (p : Pattern) (ha : d130174 p = 1) (hb : d188253 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130169 q = 1) (hb : d188248 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d130169, d188248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42479 q ha hb
    | true =>
      simp only [d130169, d188248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130170 q = 1) (hb : d188249 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d130170, d188249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130170, d188249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130171 q = 1) (hb : d188250 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d130171, d188250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130171, d188250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130172 q = 1) (hb : d188251 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d130172, d188251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130172, d188251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130173 q = 1) (hb : d188252 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d130173, d188252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130173, d188252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130174 q = 1) (hb : d188253 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d130174, d188253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130174, d188253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42481 (p : Pattern) (ha : d130180 p = 1) (hb : d188259 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130175 q = 1) (hb : d188254 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d130175, d188254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42480 q ha hb
    | true =>
      simp only [d130175, d188254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130176 q = 1) (hb : d188255 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d130176, d188255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130176, d188255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130177 q = 1) (hb : d188256 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d130177, d188256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130177, d188256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130178 q = 1) (hb : d188257 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d130178, d188257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130178, d188257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130179 q = 1) (hb : d188258 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d130179, d188258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130179, d188258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130180 q = 1) (hb : d188259 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d130180, d188259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130180, d188259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42482 (p : Pattern) (ha : d130186 p = 1) (hb : d188265 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130181 q = 1) (hb : d188260 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d130181, d188260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42481 q ha hb
    | true =>
      simp only [d130181, d188260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130182 q = 1) (hb : d188261 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d130182, d188261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130182, d188261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130183 q = 1) (hb : d188262 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d130183, d188262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130183, d188262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130184 q = 1) (hb : d188263 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d130184, d188263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130184, d188263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130185 q = 1) (hb : d188264 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d130185, d188264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130185, d188264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130186 q = 1) (hb : d188265 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d130186, d188265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130186, d188265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42483 (p : Pattern) (ha : d130192 p = 1) (hb : d188271 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130187 q = 1) (hb : d188266 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d130187, d188266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42482 q ha hb
    | true =>
      simp only [d130187, d188266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130188 q = 1) (hb : d188267 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d130188, d188267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130188, d188267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130189 q = 1) (hb : d188268 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d130189, d188268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130189, d188268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130190 q = 1) (hb : d188269 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d130190, d188269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130190, d188269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130191 q = 1) (hb : d188270 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d130191, d188270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130191, d188270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130192 q = 1) (hb : d188271 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d130192, d188271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130192, d188271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42484 (p : Pattern) (ha : d130198 p = 1) (hb : d188277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130193 q = 1) (hb : d188272 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d130193, d188272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42483 q ha hb
    | true =>
      simp only [d130193, d188272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130194 q = 1) (hb : d188273 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d130194, d188273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130194, d188273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130195 q = 1) (hb : d188274 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d130195, d188274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130195, d188274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130196 q = 1) (hb : d188275 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d130196, d188275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130196, d188275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130197 q = 1) (hb : d188276 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d130197, d188276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130197, d188276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130198 q = 1) (hb : d188277 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d130198, d188277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130198, d188277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42485 (p : Pattern) (ha : d130204 p = 1) (hb : d188283 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130199 q = 1) (hb : d188278 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d130199, d188278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42484 q ha hb
    | true =>
      simp only [d130199, d188278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130200 q = 1) (hb : d188279 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d130200, d188279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130200, d188279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130201 q = 1) (hb : d188280 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d130201, d188280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130201, d188280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130202 q = 1) (hb : d188281 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d130202, d188281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130202, d188281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130203 q = 1) (hb : d188282 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d130203, d188282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130203, d188282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130204 q = 1) (hb : d188283 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d130204, d188283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130204, d188283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42486 (p : Pattern) (ha : d130210 p = 1) (hb : d188289 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d130205 q = 1) (hb : d188284 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d130205, d188284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42485 q ha hb
    | true =>
      simp only [d130205, d188284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d130206 q = 1) (hb : d188285 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d130206, d188285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d130206, d188285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d130207 q = 1) (hb : d188286 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d130207, d188286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d130207, d188286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d130208 q = 1) (hb : d188287 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d130208, d188287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d130208, d188287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d130209 q = 1) (hb : d188288 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d130209, d188288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d130209, d188288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d130210 q = 1) (hb : d188289 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d130210, d188289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d130210, d188289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro42487 (p : Pattern) (ha : d131098 p = 1) (hb : d187684 p = 1) : d188294 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18696 q = 1) (hb : d131098 q = 1) : d187951 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d18696, d187951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d18696, d187951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42304 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d187680 q = 1) : d188290 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187680, d188290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d187680, d188290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d187681 q = 1) : d188291 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187681, d188291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187681, d188291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d187682 q = 1) : d188292 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187682, d188292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187682, d188292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d187683 q = 1) : d188293 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187683, d188293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187683, d188293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d187684 q = 1) : d188294 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187684, d188294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187684, d188294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42488 (p : Pattern) (ha : d131098 p = 1) (hb : d187694 p = 1) : d188304 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d18592 q = 1) (hb : d131098 q = 1) : d187909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d18592, d187909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42301 q ha hb
    | true =>
      simp only [d18592, d187909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42296 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d187690 q = 1) : d188300 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187690, d188300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187690, d188300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d187691 q = 1) : d188301 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187691, d188301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187691, d188301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d187692 q = 1) : d188302 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187692, d188302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187692, d188302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d187693 q = 1) : d188303 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187693, d188303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187693, d188303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d187694 q = 1) : d188304 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187694, d188304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187694, d188304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42489 (p : Pattern) (ha : d131098 p = 1) (hb : d187700 p = 1) : d188310 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d187695 q = 1) : d188305 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187695, d188305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187695, d188305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42488 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d187696 q = 1) : d188306 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187696, d188306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187696, d188306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d187697 q = 1) : d188307 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187697, d188307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187697, d188307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d187698 q = 1) : d188308 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187698, d188308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187698, d188308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d187699 q = 1) : d188309 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187699, d188309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187699, d188309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d187700 q = 1) : d188310 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187700, d188310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187700, d188310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42490 (p : Pattern) (ha : d131098 p = 1) (hb : d187706 p = 1) : d188316 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d187685 q = 1) : d188295 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187685, d188295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187685, d188295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42487 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d187686 q = 1) : d188296 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187686, d188296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187686, d188296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d187687 q = 1) : d188297 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187687, d188297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187687, d188297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d187688 q = 1) : d188298 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187688, d188298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187688, d188298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d187689 q = 1) : d188299 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187689, d188299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187689, d188299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d187701 q = 1) : d188311 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187701, d188311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187701, d188311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42489 q ha hb
  have h7 (q : Pattern) (ha : d131098 q = 1) (hb : d187702 q = 1) : d188312 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187702, d188312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187702, d188312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d131098 q = 1) (hb : d187703 q = 1) : d188313 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187703, d188313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187703, d188313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d131098 q = 1) (hb : d187704 q = 1) : d188314 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187704, d188314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187704, d188314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d131098 q = 1) (hb : d187705 q = 1) : d188315 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187705, d188315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187705, d188315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d131098 q = 1) (hb : d187706 q = 1) : d188316 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187706, d188316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187706, d188316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro42491 (p : Pattern) (ha : d131098 p = 1) (hb : d187712 p = 1) : d188322 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d187707 q = 1) : d188317 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d187707, d188317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42320 q hb ha
    | true =>
      simp only [d187707, d188317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42313 q hb ha
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d187708 q = 1) : d188318 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187708, d188318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187708, d188318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d187709 q = 1) : d188319 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187709, d188319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187709, d188319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d187710 q = 1) : d188320 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187710, d188320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187710, d188320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d187711 q = 1) : d188321 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187711, d188321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187711, d188321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d187712 q = 1) : d188322 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187712, d188322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187712, d188322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42492 (p : Pattern) (ha : d131098 p = 1) (hb : d187718 p = 1) : d188328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d187713 q = 1) : d188323 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187713, d188323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187713, d188323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42491 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d187714 q = 1) : d188324 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187714, d188324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187714, d188324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d187715 q = 1) : d188325 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187715, d188325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187715, d188325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d187716 q = 1) : d188326 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187716, d188326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187716, d188326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d187717 q = 1) : d188327 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187717, d188327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187717, d188327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d187718 q = 1) : d188328 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187718, d188328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187718, d188328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42493 (p : Pattern) (ha : d131098 p = 1) (hb : d187724 p = 1) : d188334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d187719 q = 1) : d188329 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187719, d188329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187719, d188329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42492 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d187720 q = 1) : d188330 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187720, d188330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187720, d188330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d187721 q = 1) : d188331 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187721, d188331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187721, d188331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d187722 q = 1) : d188332 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187722, d188332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187722, d188332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d187723 q = 1) : d188333 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187723, d188333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187723, d188333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d187724 q = 1) : d188334 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187724, d188334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187724, d188334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42494 (p : Pattern) (ha : d131098 p = 1) (hb : d187731 p = 1) : d188341 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d187726 q = 1) : d188336 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d187726, d188336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42336 q hb ha
    | true =>
      simp only [d187726, d188336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42328 q hb ha
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d187727 q = 1) : d188337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187727, d188337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187727, d188337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d187728 q = 1) : d188338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187728, d188338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187728, d188338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d187729 q = 1) : d188339 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187729, d188339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187729, d188339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d187730 q = 1) : d188340 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187730, d188340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187730, d188340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d187731 q = 1) : d188341 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187731, d188341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187731, d188341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42495 (p : Pattern) (ha : d131098 p = 1) (hb : d187737 p = 1) : d188347 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d187732 q = 1) : d188342 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d187732, d188342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187732, d188342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42494 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d187733 q = 1) : d188343 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d187733, d188343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d187733, d188343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d187734 q = 1) : d188344 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d187734, d188344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187734, d188344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d187735 q = 1) : d188345 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d187735, d188345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d187735, d188345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d187736 q = 1) : d188346 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d187736, d188346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d187736, d188346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d187737 q = 1) : d188347 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d187737, d188347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187737, d188347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42496 (p : Pattern) (ha : d131098 p = 1) (hb : d187743 p = 1) : d188353 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d187738 q = 1) : d188348 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d187738, d188348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187738, d188348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42495 q ha hb
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d187739 q = 1) : d188349 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d187739, d188349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187739, d188349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d187740 q = 1) : d188350 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d187740, d188350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187740, d188350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d187741 q = 1) : d188351 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d187741, d188351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187741, d188351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d187742 q = 1) : d188352 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d187742, d188352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187742, d188352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d187743 q = 1) : d188353 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d187743, d188353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187743, d188353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro42497 (p : Pattern) (ha : d131098 p = 1) (hb : d187747 p = 1) : d188356 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d19039 q = 1) (hb : d131098 q = 1) : d16444 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19039, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42347 q ha hb
    | true =>
      simp only [d19039, d16444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42341 q ha hb
  have h2 (q : Pattern) (ha : d19040 q = 1) (hb : d131098 q = 1) : d16445 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19040, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19040, d16445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19041 q = 1) (hb : d131098 q = 1) : d16446 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19041, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19041, d16446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d19051 q = 1) (hb : d131098 q = 1) : d16447 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19051, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42341 q ha hb
    | true =>
      simp only [d19051, d16447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42349 q ha hb
  have h5 (q : Pattern) (ha : d19052 q = 1) (hb : d131098 q = 1) : d16448 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19052, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19052, d16448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d19053 q = 1) (hb : d131098 q = 1) : d16449 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19053, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19053, d16449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19054 q = 1) (hb : d131098 q = 1) : d16450 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19054, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d19054, d16450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d19083 q = 1) (hb : d131098 q = 1) : d16451 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d19083, d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42341 q ha hb
    | true =>
      simp only [d19083, d16451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42342 q ha hb
  have h9 (q : Pattern) (ha : d19084 q = 1) (hb : d131098 q = 1) : d16452 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d19084, d16452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19084, d16452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d19085 q = 1) (hb : d131098 q = 1) : d16453 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d19085, d16453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19085, d16453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d19086 q = 1) (hb : d131098 q = 1) : d16454 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d19086, d16454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d19086, d16454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d131098 q = 1) (hb : d187746 q = 1) : d16455 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d187746, d16455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d187746, d16455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d131098 q = 1) (hb : d132455 q = 1) : d132455 q = 1 := by
    exact hb
  have h14 (q : Pattern) (ha : d131098 q = 1) (hb : d187747 q = 1) : d188356 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d187747, d188356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d187747, d188356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro42498 (p : Pattern) (ha : d131098 p = 1) (hb : d187753 p = 1) : d188362 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d187748 q = 1) : d188357 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d187748, d188357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42497 q ha hb
    | true =>
      simp only [d187748, d188357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d187749 q = 1) : d188358 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d187749, d188358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187749, d188358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d19093 q = 1) (hb : d131098 q = 1) : d188081 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d19093, d188081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42343 q ha hb
    | true =>
      simp only [d19093, d188081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d19094 q = 1) (hb : d131098 q = 1) : d188082 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d19094, d188082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d19094, d188082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d187750 q = 1) : d188359 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d187750, d188359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187750, d188359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d187751 q = 1) : d188360 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d187751, d188360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d187751, d188360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d131098 q = 1) (hb : d187752 q = 1) : d188361 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d187752, d188361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d187752, d188361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d131098 q = 1) (hb : d187753 q = 1) : d188362 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d187753, d188362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d187753, d188362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro42499 (p : Pattern) (ha : d131098 p = 1) (hb : d187759 p = 1) : d188368 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d131098 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d131098 q = 1) (hb : d187754 q = 1) : d188363 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d187754, d188363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42498 q ha hb
    | true =>
      simp only [d187754, d188363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro42344 q hb ha
  have h2 (q : Pattern) (ha : d131098 q = 1) (hb : d187755 q = 1) : d188364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d187755, d188364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187755, d188364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d131098 q = 1) (hb : d187756 q = 1) : d188365 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d187756, d188365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d187756, d188365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d131098 q = 1) (hb : d187757 q = 1) : d188366 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d187757, d188366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187757, d188366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d131098 q = 1) (hb : d187758 q = 1) : d188367 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d187758, d188367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187758, d188367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d131098 q = 1) (hb : d187759 q = 1) : d188368 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d187759, d188368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d187759, d188368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
