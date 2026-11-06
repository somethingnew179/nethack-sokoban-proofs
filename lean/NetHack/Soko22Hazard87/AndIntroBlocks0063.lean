import NetHack.Soko22Hazard87.AndIntroBlocks0062
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro15750 (p : Pattern) (ha : d806 p = 1) (hb : d85721 p = 1) : d11142 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d85721 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15736 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d85721 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d85721 q = 1) : d11116 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d85721 q = 1) : d11117 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d85721 q = 1) : d11141 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d11141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d11141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d806 q = 1) (hb : d85721 q = 1) : d11142 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d806, d11142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d806, d11142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15751 (p : Pattern) (ha : d813 p = 1) (hb : d85721 p = 1) : d11149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d85721 q = 1) : d11106 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d11106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15735 q ha hb
    | true =>
      simp only [d770, d11106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d85721 q = 1) : d11107 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d11107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d11107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d85721 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15736 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d85721 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d85721 q = 1) : d11112 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d11112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d11112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d811 q = 1) (hb : d85721 q = 1) : d11147 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d811, d11147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d811, d11147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d812 q = 1) (hb : d85721 q = 1) : d11148 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d812, d11148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d812, d11148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d813 q = 1) (hb : d85721 q = 1) : d11149 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d813, d11149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d813, d11149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15752 (p : Pattern) (ha : d816 p = 1) (hb : d85721 p = 1) : d11152 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d85721 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15736 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d85721 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d85721 q = 1) : d11116 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d85721 q = 1) : d11150 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d11150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d11150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d85721 q = 1) : d11151 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d11151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d11151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d816 q = 1) (hb : d85721 q = 1) : d11152 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d816, d11152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d816, d11152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15753 (p : Pattern) (ha : d845 p = 1) (hb : d85721 p = 1) : d11161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d839 q = 1) : d839 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d756 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d840 q = 1) (hb : d85721 q = 1) : d11156 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d840, d85721, d11156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d840, d85721, d11156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d841 q = 1) (hb : d85721 q = 1) : d11157 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d841, d11157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d841, d11157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d842 q = 1) (hb : d85721 q = 1) : d11158 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d842, d11158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d842, d11158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d756 q = 1) : d756 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d758 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d759 q = 1) (hb : d85721 q = 1) : d11096 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d85721, d11096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d759, d85721, d11096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d760 q = 1) (hb : d85721 q = 1) : d11097 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d11097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d11097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d761 q = 1) (hb : d85721 q = 1) : d11098 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d11098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d11098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d843 q = 1) (hb : d85721 q = 1) : d11159 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d843, d11159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d843, d11159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d758 q = 1) : d758 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d762 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d763 q = 1) (hb : d85721 q = 1) : d11099 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d85721, d11099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d763, d85721, d11099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d764 q = 1) (hb : d85721 q = 1) : d11100 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d11100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d11100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d765 q = 1) (hb : d85721 q = 1) : d11101 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d11101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d11101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d766 q = 1) (hb : d85721 q = 1) : d11102 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d766, d11102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d766, d11102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d844 q = 1) (hb : d85721 q = 1) : d11160 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d844, d11160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d844, d11160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d845 q = 1) (hb : d85721 q = 1) : d11161 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d845, d11161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d845, d11161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h19 p ha hb
theorem andIntro15754 (p : Pattern) (ha : d851 p = 1) (hb : d85721 p = 1) : d11167 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d846 q = 1) (hb : d85721 q = 1) : d11162 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, d11162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15753 q ha hb
    | true =>
      simp only [d846, d11162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d847 q = 1) (hb : d85721 q = 1) : d11163 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d847, d11163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d847, d11163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d770 q = 1) (hb : d85721 q = 1) : d11106 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d11106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15735 q ha hb
    | true =>
      simp only [d770, d11106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d771 q = 1) (hb : d85721 q = 1) : d11107 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d11107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d11107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d848 q = 1) (hb : d85721 q = 1) : d11164 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d848, d11164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d848, d11164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d849 q = 1) (hb : d85721 q = 1) : d11165 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d849, d11165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d849, d11165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d850 q = 1) (hb : d85721 q = 1) : d11166 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d850, d11166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d850, d11166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d851 q = 1) (hb : d85721 q = 1) : d11167 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d851, d11167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d851, d11167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15755 (p : Pattern) (ha : d5463 p = 1) (hb : d85721 p = 1) : d11200 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d756 q = 1) : d756 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d758 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d759 q = 1) (hb : d85721 q = 1) : d11096 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d759, d85721, d11096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d759, d85721, d11096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d760 q = 1) (hb : d85721 q = 1) : d11097 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d760, d11097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d760, d11097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d761 q = 1) (hb : d85721 q = 1) : d11098 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d761, d11098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d761, d11098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d758 q = 1) : d758 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d762 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d763 q = 1) (hb : d85721 q = 1) : d11099 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d763, d85721, d11099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d763, d85721, d11099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d764 q = 1) (hb : d85721 q = 1) : d11100 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d764, d11100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d764, d11100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d765 q = 1) (hb : d85721 q = 1) : d11101 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d765, d11101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d765, d11101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d766 q = 1) (hb : d85721 q = 1) : d11102 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d766, d11102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d766, d11102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d5456 q = 1) : d5456 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d5457 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d5458 q = 1) (hb : d85721 q = 1) : d11195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5458, d85721, d11195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d5458, d85721, d11195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d5459 q = 1) (hb : d85721 q = 1) : d11196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5459, d11196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5459, d11196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d5460 q = 1) (hb : d85721 q = 1) : d11197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5460, d11197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5460, d11197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5461 q = 1) (hb : d85721 q = 1) : d11198 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5461, d11198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5461, d11198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5462 q = 1) (hb : d85721 q = 1) : d11199 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5462, d11199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5462, d11199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5463 q = 1) (hb : d85721 q = 1) : d11200 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5463, d11200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5463, d11200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h19 p ha hb
theorem andIntro15756 (p : Pattern) (ha : d5469 p = 1) (hb : d85721 p = 1) : d11206 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5464 q = 1) (hb : d85721 q = 1) : d11201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5464, d11201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15755 q ha hb
    | true =>
      simp only [d5464, d11201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5465 q = 1) (hb : d85721 q = 1) : d11202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5465, d11202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5465, d11202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5466 q = 1) (hb : d85721 q = 1) : d11203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5466, d11203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5466, d11203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5467 q = 1) (hb : d85721 q = 1) : d11204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5467, d11204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5467, d11204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5468 q = 1) (hb : d85721 q = 1) : d11205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5468, d11205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5468, d11205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5469 q = 1) (hb : d85721 q = 1) : d11206 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5469, d11206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5469, d11206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15757 (p : Pattern) (ha : d74652 p = 1) (hb : d85721 p = 1) : d108901 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d807 q = 1) (hb : d85721 q = 1) : d11143 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d11143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15749 q ha hb
    | true =>
      simp only [d807, d11143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15750 q ha hb
  have h2 (q : Pattern) (ha : d808 q = 1) (hb : d85721 q = 1) : d11144 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d11144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d808, d11144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d809 q = 1) (hb : d85721 q = 1) : d11145 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d11145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d809, d11145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d810 q = 1) (hb : d85721 q = 1) : d11146 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d11146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, d11146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d817 q = 1) (hb : d85721 q = 1) : d11153 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d11153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15751 q ha hb
    | true =>
      simp only [d817, d11153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15752 q ha hb
  have h6 (q : Pattern) (ha : d818 q = 1) (hb : d85721 q = 1) : d11154 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d11154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, d11154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d819 q = 1) (hb : d85721 q = 1) : d11155 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d11155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d819, d11155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d852 q = 1) (hb : d85721 q = 1) : d11168 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d11168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15754 q ha hb
    | true =>
      simp only [d852, d11168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15737 q ha hb
  have h9 (q : Pattern) (ha : d4446 q = 1) (hb : d85721 q = 1) : d108897 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d108897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4446, d108897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5470 q = 1) (hb : d85721 q = 1) : d11207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5470, d11207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15756 q ha hb
    | true =>
      simp only [d5470, d11207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5471 q = 1) (hb : d85721 q = 1) : d11208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5471, d11208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5471, d11208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74649 q = 1) (hb : d85721 q = 1) : d108898 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74649, d108898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74649, d108898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74650 q = 1) (hb : d85721 q = 1) : d108899 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74650, d108899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74650, d108899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74651 q = 1) (hb : d85721 q = 1) : d108900 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74651, d108900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74651, d108900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74652 q = 1) (hb : d85721 q = 1) : d108901 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74652, d108901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74652, d108901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro15758 (p : Pattern) (ha : d915 p = 1) (hb : d85721 p = 1) : d11213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d85721 q = 1) : d11106 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d11106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15735 q ha hb
    | true =>
      simp only [d770, d11106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d85721 q = 1) : d11107 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d11107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d11107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d85721 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15736 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d85721 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d85721 q = 1) : d11112 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d11112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d11112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d777 q = 1) (hb : d85721 q = 1) : d11113 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d777, d11113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d777, d11113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d803 q = 1) (hb : d85721 q = 1) : d11139 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d803, d11139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d803, d11139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d915 q = 1) (hb : d85721 q = 1) : d11213 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d915, d11213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d915, d11213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15759 (p : Pattern) (ha : d916 p = 1) (hb : d85721 p = 1) : d11214 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d85721 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15736 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d85721 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d85721 q = 1) : d11116 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d781 q = 1) (hb : d85721 q = 1) : d11117 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d781, d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d781, d11117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d805 q = 1) (hb : d85721 q = 1) : d11141 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d805, d11141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d805, d11141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d916 q = 1) (hb : d85721 q = 1) : d11214 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d916, d11214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d916, d11214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15760 (p : Pattern) (ha : d921 p = 1) (hb : d85721 p = 1) : d11219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d770 q = 1) (hb : d85721 q = 1) : d11106 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d11106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15735 q ha hb
    | true =>
      simp only [d770, d11106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d771 q = 1) (hb : d85721 q = 1) : d11107 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d11107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d11107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d774 q = 1) (hb : d85721 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15736 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d775 q = 1) (hb : d85721 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d776 q = 1) (hb : d85721 q = 1) : d11112 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d776, d11112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d776, d11112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d811 q = 1) (hb : d85721 q = 1) : d11147 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d811, d11147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d811, d11147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d812 q = 1) (hb : d85721 q = 1) : d11148 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d812, d11148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d812, d11148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d921 q = 1) (hb : d85721 q = 1) : d11219 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d921, d11219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d921, d11219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15761 (p : Pattern) (ha : d922 p = 1) (hb : d85721 p = 1) : d11220 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d774 q = 1) (hb : d85721 q = 1) : d11110 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15736 q ha hb
    | true =>
      simp only [d774, d11110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d775 q = 1) (hb : d85721 q = 1) : d11111 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d775, d11111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d780 q = 1) (hb : d85721 q = 1) : d11116 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d780, d11116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d814 q = 1) (hb : d85721 q = 1) : d11150 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d814, d11150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d814, d11150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d815 q = 1) (hb : d85721 q = 1) : d11151 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d815, d11151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d815, d11151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d922 q = 1) (hb : d85721 q = 1) : d11220 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d922, d11220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d922, d11220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15762 (p : Pattern) (ha : d926 p = 1) (hb : d85721 p = 1) : d11224 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d846 q = 1) (hb : d85721 q = 1) : d11162 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d846, d11162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15753 q ha hb
    | true =>
      simp only [d846, d11162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d847 q = 1) (hb : d85721 q = 1) : d11163 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d847, d11163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d847, d11163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d770 q = 1) (hb : d85721 q = 1) : d11106 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d770, d11106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15735 q ha hb
    | true =>
      simp only [d770, d11106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d771 q = 1) (hb : d85721 q = 1) : d11107 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d771, d11107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d771, d11107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d848 q = 1) (hb : d85721 q = 1) : d11164 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d848, d11164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d848, d11164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d849 q = 1) (hb : d85721 q = 1) : d11165 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d849, d11165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d849, d11165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d850 q = 1) (hb : d85721 q = 1) : d11166 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d850, d11166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d850, d11166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d926 q = 1) (hb : d85721 q = 1) : d11224 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d926, d11224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d926, d11224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15763 (p : Pattern) (ha : d5476 p = 1) (hb : d85721 p = 1) : d11230 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5464 q = 1) (hb : d85721 q = 1) : d11201 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5464, d11201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15755 q ha hb
    | true =>
      simp only [d5464, d11201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5465 q = 1) (hb : d85721 q = 1) : d11202 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5465, d11202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5465, d11202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5466 q = 1) (hb : d85721 q = 1) : d11203 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5466, d11203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5466, d11203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5467 q = 1) (hb : d85721 q = 1) : d11204 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5467, d11204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5467, d11204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5468 q = 1) (hb : d85721 q = 1) : d11205 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5468, d11205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5468, d11205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5476 q = 1) (hb : d85721 q = 1) : d11230 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5476, d11230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5476, d11230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15764 (p : Pattern) (ha : d74656 p = 1) (hb : d85721 p = 1) : d108906 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d807 q = 1) (hb : d85721 q = 1) : d11143 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d807, d11143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15749 q ha hb
    | true =>
      simp only [d807, d11143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15750 q ha hb
  have h2 (q : Pattern) (ha : d808 q = 1) (hb : d85721 q = 1) : d11144 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d808, d11144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d808, d11144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d809 q = 1) (hb : d85721 q = 1) : d11145 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d809, d11145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d809, d11145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d810 q = 1) (hb : d85721 q = 1) : d11146 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d810, d11146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d810, d11146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d817 q = 1) (hb : d85721 q = 1) : d11153 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d817, d11153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15751 q ha hb
    | true =>
      simp only [d817, d11153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15752 q ha hb
  have h6 (q : Pattern) (ha : d818 q = 1) (hb : d85721 q = 1) : d11154 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d818, d11154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d818, d11154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d819 q = 1) (hb : d85721 q = 1) : d11155 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d819, d11155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d819, d11155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d852 q = 1) (hb : d85721 q = 1) : d11168 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d852, d11168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15754 q ha hb
    | true =>
      simp only [d852, d11168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15737 q ha hb
  have h9 (q : Pattern) (ha : d4446 q = 1) (hb : d85721 q = 1) : d108897 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4446, d108897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4446, d108897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5470 q = 1) (hb : d85721 q = 1) : d11207 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5470, d11207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15756 q ha hb
    | true =>
      simp only [d5470, d11207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5471 q = 1) (hb : d85721 q = 1) : d11208 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5471, d11208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5471, d11208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74649 q = 1) (hb : d85721 q = 1) : d108898 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74649, d108898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74649, d108898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74650 q = 1) (hb : d85721 q = 1) : d108899 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74650, d108899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74650, d108899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74651 q = 1) (hb : d85721 q = 1) : d108900 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74651, d108900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74651, d108900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d917 q = 1) (hb : d85721 q = 1) : d11215 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d917, d11215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15758 q ha hb
    | true =>
      simp only [d917, d11215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15759 q ha hb
  have h16 (q : Pattern) (ha : d918 q = 1) (hb : d85721 q = 1) : d11216 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d918, d11216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d918, d11216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d919 q = 1) (hb : d85721 q = 1) : d11217 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d919, d11217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d919, d11217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d920 q = 1) (hb : d85721 q = 1) : d11218 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d920, d11218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d920, d11218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d923 q = 1) (hb : d85721 q = 1) : d11221 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d923, d11221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15760 q ha hb
    | true =>
      simp only [d923, d11221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15761 q ha hb
  have h20 (q : Pattern) (ha : d924 q = 1) (hb : d85721 q = 1) : d11222 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d924, d11222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d924, d11222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d925 q = 1) (hb : d85721 q = 1) : d11223 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d925, d11223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d925, d11223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d927 q = 1) (hb : d85721 q = 1) : d11225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d11225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15762 q ha hb
    | true =>
      simp only [d927, d11225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15740 q ha hb
  have h23 (q : Pattern) (ha : d4451 q = 1) (hb : d85721 q = 1) : d108902 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d108902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4451, d108902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5477 q = 1) (hb : d85721 q = 1) : d11231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5477, d11231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15763 q ha hb
    | true =>
      simp only [d5477, d11231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5478 q = 1) (hb : d85721 q = 1) : d11232 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5478, d11232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5478, d11232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d74653 q = 1) (hb : d85721 q = 1) : d108903 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74653, d108903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d74653, d108903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d74654 q = 1) (hb : d85721 q = 1) : d108904 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74654, d108904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74654, d108904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d74655 q = 1) (hb : d85721 q = 1) : d108905 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74655, d108905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74655, d108905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d74656 q = 1) (hb : d85721 q = 1) : d108906 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74656, d108906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74656, d108906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro15765 (p : Pattern) (ha : d74663 p = 1) (hb : d85721 p = 1) : d108913 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d927 q = 1) (hb : d85721 q = 1) : d11225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d927, d11225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15762 q ha hb
    | true =>
      simp only [d927, d11225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15740 q ha hb
  have h2 (q : Pattern) (ha : d4451 q = 1) (hb : d85721 q = 1) : d108902 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4451, d108902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4451, d108902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5477 q = 1) (hb : d85721 q = 1) : d11231 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5477, d11231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15763 q ha hb
    | true =>
      simp only [d5477, d11231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5478 q = 1) (hb : d85721 q = 1) : d11232 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5478, d11232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5478, d11232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74653 q = 1) (hb : d85721 q = 1) : d108903 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74653, d108903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74653, d108903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74661 q = 1) (hb : d85721 q = 1) : d108911 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74661, d108911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74661, d108911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74662 q = 1) (hb : d85721 q = 1) : d108912 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74662, d108912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74662, d108912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74663 q = 1) (hb : d85721 q = 1) : d108913 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74663, d108913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74663, d108913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15766 (p : Pattern) (ha : d992 p = 1) (hb : d85721 p = 1) : d11276 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d970 q = 1) : d970 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d976 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d977 q = 1) (hb : d85721 q = 1) : d11264 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d977, d85721, d11264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d977, d85721, d11264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d978 q = 1) (hb : d85721 q = 1) : d11265 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d978, d11265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d978, d11265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d979 q = 1) (hb : d85721 q = 1) : d11266 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d979, d11266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d979, d11266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d976 q = 1) : d976 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d981 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d982 q = 1) (hb : d85721 q = 1) : d11267 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d85721, d11267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d982, d85721, d11267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d983 q = 1) (hb : d85721 q = 1) : d11268 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d11268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d11268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d984 q = 1) (hb : d85721 q = 1) : d11269 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d11269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d11269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d985 q = 1) (hb : d85721 q = 1) : d11270 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d985, d11270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d985, d11270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d981 q = 1) : d981 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d986 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d987 q = 1) (hb : d85721 q = 1) : d11271 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d85721, d11271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d987, d85721, d11271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d988 q = 1) (hb : d85721 q = 1) : d11272 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d11272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d11272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d989 q = 1) (hb : d85721 q = 1) : d11273 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d11273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d11273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d990 q = 1) (hb : d85721 q = 1) : d11274 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d11274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d990, d11274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d991 q = 1) (hb : d85721 q = 1) : d11275 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d991, d11275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d991, d11275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d992 q = 1) (hb : d85721 q = 1) : d11276 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d992, d11276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d992, d11276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h19 p ha hb
theorem andIntro15767 (p : Pattern) (ha : d997 p = 1) (hb : d85721 p = 1) : d11281 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d976 q = 1) : d976 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d981 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d982 q = 1) (hb : d85721 q = 1) : d11267 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d85721, d11267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d982, d85721, d11267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d983 q = 1) (hb : d85721 q = 1) : d11268 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d11268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d11268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d984 q = 1) (hb : d85721 q = 1) : d11269 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d11269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d11269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d981 q = 1) : d981 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d986 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d987 q = 1) (hb : d85721 q = 1) : d11271 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d85721, d11271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d987, d85721, d11271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d988 q = 1) (hb : d85721 q = 1) : d11272 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d11272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d11272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d989 q = 1) (hb : d85721 q = 1) : d11273 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d11273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d11273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d990 q = 1) (hb : d85721 q = 1) : d11274 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d11274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d990, d11274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d995 q = 1) (hb : d85721 q = 1) : d11279 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d995, d11279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d995, d11279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d996 q = 1) (hb : d85721 q = 1) : d11280 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d996, d11280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d996, d11280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d997 q = 1) (hb : d85721 q = 1) : d11281 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d997, d11281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d997, d11281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro15768 (p : Pattern) (ha : d1003 p = 1) (hb : d85721 p = 1) : d11287 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d993 q = 1) (hb : d85721 q = 1) : d11277 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d993, d11277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15766 q ha hb
    | true =>
      simp only [d993, d11277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d994 q = 1) (hb : d85721 q = 1) : d11278 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d994, d11278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d994, d11278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d998 q = 1) (hb : d85721 q = 1) : d11282 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d998, d11282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15767 q ha hb
    | true =>
      simp only [d998, d11282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d999 q = 1) (hb : d85721 q = 1) : d11283 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d999, d11283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d999, d11283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1000 q = 1) (hb : d85721 q = 1) : d11284 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1000, d11284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1000, d11284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1001 q = 1) (hb : d85721 q = 1) : d11285 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1001, d11285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1001, d11285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1002 q = 1) (hb : d85721 q = 1) : d11286 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1002, d11286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1002, d11286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1003 q = 1) (hb : d85721 q = 1) : d11287 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1003, d11287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1003, d11287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15769 (p : Pattern) (ha : d1011 p = 1) (hb : d85721 p = 1) : d11295 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d998 q = 1) (hb : d85721 q = 1) : d11282 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d998, d11282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15767 q ha hb
    | true =>
      simp only [d998, d11282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d999 q = 1) (hb : d85721 q = 1) : d11283 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d999, d11283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d999, d11283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1006 q = 1) (hb : d85721 q = 1) : d11290 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1006, d11290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15746 q ha hb
    | true =>
      simp only [d1006, d11290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1007 q = 1) (hb : d85721 q = 1) : d11291 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1007, d11291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1007, d11291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1008 q = 1) (hb : d85721 q = 1) : d11292 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1008, d11292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1008, d11292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1009 q = 1) (hb : d85721 q = 1) : d11293 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1009, d11293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1009, d11293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1010 q = 1) (hb : d85721 q = 1) : d11294 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1010, d11294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1010, d11294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1011 q = 1) (hb : d85721 q = 1) : d11295 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1011, d11295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1011, d11295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15770 (p : Pattern) (ha : d5507 p = 1) (hb : d85721 p = 1) : d11328 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d976 q = 1) : d976 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d981 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d982 q = 1) (hb : d85721 q = 1) : d11267 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d982, d85721, d11267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d982, d85721, d11267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d983 q = 1) (hb : d85721 q = 1) : d11268 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d983, d11268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d983, d11268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d984 q = 1) (hb : d85721 q = 1) : d11269 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d984, d11269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d984, d11269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d981 q = 1) : d981 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d986 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d987 q = 1) (hb : d85721 q = 1) : d11271 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d987, d85721, d11271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d987, d85721, d11271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d988 q = 1) (hb : d85721 q = 1) : d11272 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d988, d11272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d988, d11272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d989 q = 1) (hb : d85721 q = 1) : d11273 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d989, d11273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d989, d11273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d990 q = 1) (hb : d85721 q = 1) : d11274 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d990, d11274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d990, d11274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d5500 q = 1) : d5500 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d5501 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d5502 q = 1) (hb : d85721 q = 1) : d11323 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5502, d85721, d11323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d5502, d85721, d11323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d5503 q = 1) (hb : d85721 q = 1) : d11324 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5503, d11324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5503, d11324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d5504 q = 1) (hb : d85721 q = 1) : d11325 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5504, d11325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5504, d11325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5505 q = 1) (hb : d85721 q = 1) : d11326 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5505, d11326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5505, d11326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5506 q = 1) (hb : d85721 q = 1) : d11327 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5506, d11327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5506, d11327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5507 q = 1) (hb : d85721 q = 1) : d11328 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5507, d11328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5507, d11328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h19 p ha hb
theorem andIntro15771 (p : Pattern) (ha : d5513 p = 1) (hb : d85721 p = 1) : d11334 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5508 q = 1) (hb : d85721 q = 1) : d11329 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5508, d11329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15770 q ha hb
    | true =>
      simp only [d5508, d11329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5509 q = 1) (hb : d85721 q = 1) : d11330 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5509, d11330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5509, d11330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5510 q = 1) (hb : d85721 q = 1) : d11331 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5510, d11331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5510, d11331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5511 q = 1) (hb : d85721 q = 1) : d11332 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5511, d11332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5511, d11332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5512 q = 1) (hb : d85721 q = 1) : d11333 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5512, d11333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5512, d11333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5513 q = 1) (hb : d85721 q = 1) : d11334 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5513, d11334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5513, d11334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15772 (p : Pattern) (ha : d74672 p = 1) (hb : d85721 p = 1) : d108923 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1012 q = 1) (hb : d85721 q = 1) : d11296 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1012, d11296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15768 q ha hb
    | true =>
      simp only [d1012, d11296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15769 q ha hb
  have h2 (q : Pattern) (ha : d4466 q = 1) (hb : d85721 q = 1) : d108919 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4466, d108919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4466, d108919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5514 q = 1) (hb : d85721 q = 1) : d11335 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5514, d11335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15771 q ha hb
    | true =>
      simp only [d5514, d11335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5515 q = 1) (hb : d85721 q = 1) : d11336 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5515, d11336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5515, d11336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74669 q = 1) (hb : d85721 q = 1) : d108920 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74669, d108920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74669, d108920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74670 q = 1) (hb : d85721 q = 1) : d108921 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74670, d108921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74670, d108921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74671 q = 1) (hb : d85721 q = 1) : d108922 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74671, d108922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74671, d108922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74672 q = 1) (hb : d85721 q = 1) : d108923 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74672, d108923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74672, d108923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15773 (p : Pattern) (ha : d74678 p = 1) (hb : d85721 p = 1) : d108929 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d790 q = 1) (hb : d85721 q = 1) : d11126 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d11126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d790, d11126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15739 q ha hb
  have h2 (q : Pattern) (ha : d791 q = 1) (hb : d85721 q = 1) : d11127 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d11127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d791, d11127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d800 q = 1) (hb : d85721 q = 1) : d11136 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d11136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15739 q ha hb
    | true =>
      simp only [d800, d11136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15742 q ha hb
  have h4 (q : Pattern) (ha : d801 q = 1) (hb : d85721 q = 1) : d11137 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d11137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d801, d11137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d802 q = 1) (hb : d85721 q = 1) : d11138 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d11138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d802, d11138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74657 q = 1) (hb : d85721 q = 1) : d108907 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74657, d108907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15757 q ha hb
    | true =>
      simp only [d74657, d108907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15764 q ha hb
  have h7 (q : Pattern) (ha : d951 q = 1) (hb : d85721 q = 1) : d11250 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, d11250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15743 q ha hb
    | true =>
      simp only [d951, d11250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15744 q ha hb
  have h8 (q : Pattern) (ha : d74658 q = 1) (hb : d85721 q = 1) : d108908 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74658, d108908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74658, d108908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74659 q = 1) (hb : d85721 q = 1) : d108909 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74659, d108909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74659, d108909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d74660 q = 1) (hb : d85721 q = 1) : d108910 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74660, d108910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74660, d108910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74664 q = 1) (hb : d85721 q = 1) : d108914 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74664, d108914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74664, d108914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15765 q ha hb
  have h12 (q : Pattern) (ha : d960 q = 1) (hb : d85721 q = 1) : d11259 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d11259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d960, d11259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15745 q ha hb
  have h13 (q : Pattern) (ha : d74665 q = 1) (hb : d85721 q = 1) : d108915 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74665, d108915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74665, d108915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74666 q = 1) (hb : d85721 q = 1) : d108916 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74666, d108916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74666, d108916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d74667 q = 1) (hb : d85721 q = 1) : d108917 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74667, d108917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74667, d108917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d74668 q = 1) (hb : d85721 q = 1) : d108918 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74668, d108918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74668, d108918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74673 q = 1) (hb : d85721 q = 1) : d108924 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74673, d108924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74673, d108924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15772 q ha hb
  have h18 (q : Pattern) (ha : d1070 q = 1) (hb : d85721 q = 1) : d11352 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1070, d11352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1070, d11352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15748 q ha hb
  have h19 (q : Pattern) (ha : d74674 q = 1) (hb : d85721 q = 1) : d108925 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74674, d108925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74674, d108925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d74675 q = 1) (hb : d85721 q = 1) : d108926 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74675, d108926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74675, d108926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d74676 q = 1) (hb : d85721 q = 1) : d108927 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74676, d108927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74676, d108927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d74677 q = 1) (hb : d85721 q = 1) : d108928 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74677, d108928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74677, d108928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d74678 q = 1) (hb : d85721 q = 1) : d108929 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74678, d108929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74678, d108929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro15774 (p : Pattern) (ha : d74684 p = 1) (hb : d85721 p = 1) : d108935 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74679 q = 1) (hb : d85721 q = 1) : d108930 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74679, d108930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74679, d108930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15773 q ha hb
  have h2 (q : Pattern) (ha : d74680 q = 1) (hb : d85721 q = 1) : d108931 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74680, d108931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74680, d108931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74681 q = 1) (hb : d85721 q = 1) : d108932 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74681, d108932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74681, d108932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74682 q = 1) (hb : d85721 q = 1) : d108933 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74682, d108933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74682, d108933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74683 q = 1) (hb : d85721 q = 1) : d108934 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74683, d108934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74683, d108934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74684 q = 1) (hb : d85721 q = 1) : d108935 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74684, d108935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74684, d108935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15775 (p : Pattern) (ha : d1148 p = 1) (hb : d85721 p = 1) : d11375 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1126 q = 1) : d1126 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1128 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1129 q = 1) (hb : d85721 q = 1) : d11366 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d85721, d11366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1129, d85721, d11366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1130 q = 1) (hb : d85721 q = 1) : d11367 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d11367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d11367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1131 q = 1) (hb : d85721 q = 1) : d11368 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d11368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d11368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1128 q = 1) : d1128 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1141 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1142 q = 1) (hb : d85721 q = 1) : d11369 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d85721, d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1142, d85721, d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1143 q = 1) (hb : d85721 q = 1) : d11370 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d11370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d11370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1144 q = 1) (hb : d85721 q = 1) : d11371 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d11371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d11371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1145 q = 1) (hb : d85721 q = 1) : d11372 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d11372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1145, d11372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1146 q = 1) (hb : d85721 q = 1) : d11373 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, d11373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1146, d11373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1147 q = 1) (hb : d85721 q = 1) : d11374 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1147, d11374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1147, d11374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1148 q = 1) (hb : d85721 q = 1) : d11375 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1148, d11375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1148, d11375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro15776 (p : Pattern) (ha : d1152 p = 1) (hb : d85721 p = 1) : d11379 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1128 q = 1) : d1128 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1141 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1142 q = 1) (hb : d85721 q = 1) : d11369 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d85721, d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1142, d85721, d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1143 q = 1) (hb : d85721 q = 1) : d11370 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d11370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d11370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1144 q = 1) (hb : d85721 q = 1) : d11371 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d11371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d11371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1146 q = 1) (hb : d85721 q = 1) : d11373 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1146, d11373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1146, d11373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1151 q = 1) (hb : d85721 q = 1) : d11378 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1151, d11378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1151, d11378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1152 q = 1) (hb : d85721 q = 1) : d11379 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1152, d11379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1152, d11379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15777 (p : Pattern) (ha : d1158 p = 1) (hb : d85721 p = 1) : d11385 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d85721 q = 1) : d11376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d11376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15775 q ha hb
    | true =>
      simp only [d1149, d11376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d85721 q = 1) : d11377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d11377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d11377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d85721 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15776 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d85721 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d85721 q = 1) : d11382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d11382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d11382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d85721 q = 1) : d11383 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d11383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d11383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1157 q = 1) (hb : d85721 q = 1) : d11384 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1157, d11384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1157, d11384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1158 q = 1) (hb : d85721 q = 1) : d11385 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1158, d11385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1158, d11385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15778 (p : Pattern) (ha : d1162 p = 1) (hb : d85721 p = 1) : d11389 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d85721 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15776 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d85721 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d85721 q = 1) : d11386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d85721 q = 1) : d11387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d85721 q = 1) : d11388 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, d11388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, d11388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1162 q = 1) (hb : d85721 q = 1) : d11389 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1162, d11389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1162, d11389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15779 (p : Pattern) (ha : d1168 p = 1) (hb : d85721 p = 1) : d11395 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1163 q = 1) (hb : d85721 q = 1) : d11390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d11390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15777 q ha hb
    | true =>
      simp only [d1163, d11390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15778 q ha hb
  have h2 (q : Pattern) (ha : d1164 q = 1) (hb : d85721 q = 1) : d11391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d11391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, d11391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1165 q = 1) (hb : d85721 q = 1) : d11392 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d11392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1165, d11392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1166 q = 1) (hb : d85721 q = 1) : d11393 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d11393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d11393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1167 q = 1) (hb : d85721 q = 1) : d11394 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d11394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d11394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1168 q = 1) (hb : d85721 q = 1) : d11395 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1168, d11395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1168, d11395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15780 (p : Pattern) (ha : d1171 p = 1) (hb : d85721 p = 1) : d11398 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d85721 q = 1) : d11376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d11376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15775 q ha hb
    | true =>
      simp only [d1149, d11376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d85721 q = 1) : d11377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d11377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d11377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d85721 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15776 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d85721 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d85721 q = 1) : d11382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d11382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d11382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d85721 q = 1) : d11383 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d11383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d11383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1157 q = 1) (hb : d85721 q = 1) : d11384 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1157, d11384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1157, d11384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1171 q = 1) (hb : d85721 q = 1) : d11398 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1171, d11398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1171, d11398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15781 (p : Pattern) (ha : d1172 p = 1) (hb : d85721 p = 1) : d11399 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d85721 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15776 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d85721 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d85721 q = 1) : d11386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d85721 q = 1) : d11387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1161 q = 1) (hb : d85721 q = 1) : d11388 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1161, d11388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1161, d11388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1172 q = 1) (hb : d85721 q = 1) : d11399 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1172, d11399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1172, d11399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15782 (p : Pattern) (ha : d1178 p = 1) (hb : d85721 p = 1) : d11405 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1163 q = 1) (hb : d85721 q = 1) : d11390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d11390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15777 q ha hb
    | true =>
      simp only [d1163, d11390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15778 q ha hb
  have h2 (q : Pattern) (ha : d1164 q = 1) (hb : d85721 q = 1) : d11391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d11391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, d11391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1165 q = 1) (hb : d85721 q = 1) : d11392 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d11392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1165, d11392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1166 q = 1) (hb : d85721 q = 1) : d11393 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d11393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d11393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1167 q = 1) (hb : d85721 q = 1) : d11394 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d11394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d11394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1173 q = 1) (hb : d85721 q = 1) : d11400 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1173, d11400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15780 q ha hb
    | true =>
      simp only [d1173, d11400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15781 q ha hb
  have h7 (q : Pattern) (ha : d1174 q = 1) (hb : d85721 q = 1) : d11401 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1174, d11401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1174, d11401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1175 q = 1) (hb : d85721 q = 1) : d11402 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1175, d11402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1175, d11402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1176 q = 1) (hb : d85721 q = 1) : d11403 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1176, d11403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1176, d11403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1177 q = 1) (hb : d85721 q = 1) : d11404 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1177, d11404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1177, d11404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1178 q = 1) (hb : d85721 q = 1) : d11405 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1178, d11405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1178, d11405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15783 (p : Pattern) (ha : d1355 p = 1) (hb : d85721 p = 1) : d11513 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1163 q = 1) (hb : d85721 q = 1) : d11390 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1163, d11390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15777 q ha hb
    | true =>
      simp only [d1163, d11390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15778 q ha hb
  have h2 (q : Pattern) (ha : d1164 q = 1) (hb : d85721 q = 1) : d11391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1164, d11391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1164, d11391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1165 q = 1) (hb : d85721 q = 1) : d11392 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1165, d11392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1165, d11392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1166 q = 1) (hb : d85721 q = 1) : d11393 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1166, d11393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1166, d11393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1167 q = 1) (hb : d85721 q = 1) : d11394 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1167, d11394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1167, d11394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1350 q = 1) (hb : d85721 q = 1) : d11508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d11508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15778 q ha hb
    | true =>
      simp only [d1350, d11508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1351 q = 1) (hb : d85721 q = 1) : d11509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d11509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d11509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1352 q = 1) (hb : d85721 q = 1) : d11510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d11510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1352, d11510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1353 q = 1) (hb : d85721 q = 1) : d11511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d11511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d11511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1354 q = 1) (hb : d85721 q = 1) : d11512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d11512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d11512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1355 q = 1) (hb : d85721 q = 1) : d11513 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1355, d11513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1355, d11513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15784 (p : Pattern) (ha : d1361 p = 1) (hb : d85721 p = 1) : d11519 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1350 q = 1) (hb : d85721 q = 1) : d11508 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1350, d11508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15778 q ha hb
    | true =>
      simp only [d1350, d11508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1351 q = 1) (hb : d85721 q = 1) : d11509 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1351, d11509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1351, d11509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1352 q = 1) (hb : d85721 q = 1) : d11510 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1352, d11510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1352, d11510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1353 q = 1) (hb : d85721 q = 1) : d11511 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1353, d11511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1353, d11511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1354 q = 1) (hb : d85721 q = 1) : d11512 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1354, d11512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1354, d11512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1356 q = 1) (hb : d85721 q = 1) : d11514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d11514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15781 q ha hb
    | true =>
      simp only [d1356, d11514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1357 q = 1) (hb : d85721 q = 1) : d11515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d11515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, d11515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1358 q = 1) (hb : d85721 q = 1) : d11516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d11516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1358, d11516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1359 q = 1) (hb : d85721 q = 1) : d11517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d11517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, d11517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1360 q = 1) (hb : d85721 q = 1) : d11518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d11518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, d11518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1361 q = 1) (hb : d85721 q = 1) : d11519 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1361, d11519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1361, d11519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15785 (p : Pattern) (ha : d1370 p = 1) (hb : d85721 p = 1) : d11528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1356 q = 1) (hb : d85721 q = 1) : d11514 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1356, d11514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15781 q ha hb
    | true =>
      simp only [d1356, d11514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1357 q = 1) (hb : d85721 q = 1) : d11515 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1357, d11515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1357, d11515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1358 q = 1) (hb : d85721 q = 1) : d11516 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1358, d11516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1358, d11516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1359 q = 1) (hb : d85721 q = 1) : d11517 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1359, d11517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1359, d11517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1360 q = 1) (hb : d85721 q = 1) : d11518 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1360, d11518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1360, d11518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1370 q = 1) (hb : d85721 q = 1) : d11528 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1370, d11528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1370, d11528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15786 (p : Pattern) (ha : d1430 p = 1) (hb : d85721 p = 1) : d11559 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1401 q = 1) : d1401 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1411 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1412 q = 1) (hb : d85721 q = 1) : d11541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d85721, d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1412, d85721, d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1413 q = 1) (hb : d85721 q = 1) : d11542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d11542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d11542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1414 q = 1) (hb : d85721 q = 1) : d11543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d11543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d11543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1420 q = 1) (hb : d85721 q = 1) : d11549 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d11549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1420, d11549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1429 q = 1) (hb : d85721 q = 1) : d11558 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1429, d11558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1429, d11558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1430 q = 1) (hb : d85721 q = 1) : d11559 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1430, d11559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1430, d11559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15787 (p : Pattern) (ha : d1497 p = 1) (hb : d85721 p = 1) : d11615 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1431 q = 1) (hb : d85721 q = 1) : d11560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d11560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15786 q ha hb
    | true =>
      simp only [d1431, d11560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1432 q = 1) (hb : d85721 q = 1) : d11561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d11561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d11561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1494 q = 1) (hb : d85721 q = 1) : d11612 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1494, d11612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1494, d11612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1495 q = 1) (hb : d85721 q = 1) : d11613 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1495, d11613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1495, d11613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1496 q = 1) (hb : d85721 q = 1) : d11614 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1496, d11614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1496, d11614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1497 q = 1) (hb : d85721 q = 1) : d11615 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1497, d11615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1497, d11615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15788 (p : Pattern) (ha : d1503 p = 1) (hb : d85721 p = 1) : d11621 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1498 q = 1) (hb : d85721 q = 1) : d11616 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1498, d11616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15787 q ha hb
    | true =>
      simp only [d1498, d11616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1499 q = 1) (hb : d85721 q = 1) : d11617 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1499, d11617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1499, d11617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1500 q = 1) (hb : d85721 q = 1) : d11618 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1500, d11618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1500, d11618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1501 q = 1) (hb : d85721 q = 1) : d11619 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1501, d11619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1501, d11619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1502 q = 1) (hb : d85721 q = 1) : d11620 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1502, d11620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1502, d11620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1503 q = 1) (hb : d85721 q = 1) : d11621 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1503, d11621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1503, d11621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15789 (p : Pattern) (ha : d1183 p = 1) (hb : d85721 p = 1) : d11410 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d85721 q = 1) : d11376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d11376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15775 q ha hb
    | true =>
      simp only [d1149, d11376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d85721 q = 1) : d11377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d11377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d11377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d85721 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15776 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d85721 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d85721 q = 1) : d11382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d11382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d11382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d85721 q = 1) : d11383 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d11383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d11383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1182 q = 1) (hb : d85721 q = 1) : d11409 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1182, d11409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1182, d11409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1183 q = 1) (hb : d85721 q = 1) : d11410 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1183, d11410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1183, d11410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15790 (p : Pattern) (ha : d1185 p = 1) (hb : d85721 p = 1) : d11412 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d85721 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15776 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d85721 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d85721 q = 1) : d11386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d85721 q = 1) : d11387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1184 q = 1) (hb : d85721 q = 1) : d11411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d11411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, d11411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1185 q = 1) (hb : d85721 q = 1) : d11412 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1185, d11412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1185, d11412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15791 (p : Pattern) (ha : d1192 p = 1) (hb : d85721 p = 1) : d11419 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d85721 q = 1) : d11376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d11376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15775 q ha hb
    | true =>
      simp only [d1149, d11376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d85721 q = 1) : d11377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d11377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d11377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d85721 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15776 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d85721 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d85721 q = 1) : d11382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d11382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d11382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1190 q = 1) (hb : d85721 q = 1) : d11417 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1190, d11417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1190, d11417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1191 q = 1) (hb : d85721 q = 1) : d11418 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1191, d11418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1191, d11418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1192 q = 1) (hb : d85721 q = 1) : d11419 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1192, d11419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1192, d11419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15792 (p : Pattern) (ha : d1195 p = 1) (hb : d85721 p = 1) : d11422 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d85721 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15776 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d85721 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d85721 q = 1) : d11386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1193 q = 1) (hb : d85721 q = 1) : d11420 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d11420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, d11420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1194 q = 1) (hb : d85721 q = 1) : d11421 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d11421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1194, d11421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1195 q = 1) (hb : d85721 q = 1) : d11422 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1195, d11422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1195, d11422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15793 (p : Pattern) (ha : d1221 p = 1) (hb : d85721 p = 1) : d11431 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1215 q = 1) : d1215 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1126 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1216 q = 1) (hb : d85721 q = 1) : d11426 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1216, d85721, d11426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1216, d85721, d11426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1217 q = 1) (hb : d85721 q = 1) : d11427 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1217, d11427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1217, d11427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1218 q = 1) (hb : d85721 q = 1) : d11428 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1218, d11428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1218, d11428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1126 q = 1) : d1126 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1128 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1129 q = 1) (hb : d85721 q = 1) : d11366 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d85721, d11366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1129, d85721, d11366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1130 q = 1) (hb : d85721 q = 1) : d11367 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d11367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d11367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1131 q = 1) (hb : d85721 q = 1) : d11368 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d11368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d11368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1219 q = 1) (hb : d85721 q = 1) : d11429 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1219, d11429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1219, d11429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d1128 q = 1) : d1128 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d1141 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1142 q = 1) (hb : d85721 q = 1) : d11369 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d85721, d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1142, d85721, d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d1143 q = 1) (hb : d85721 q = 1) : d11370 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d11370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d11370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1144 q = 1) (hb : d85721 q = 1) : d11371 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d11371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d11371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1145 q = 1) (hb : d85721 q = 1) : d11372 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d11372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1145, d11372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1220 q = 1) (hb : d85721 q = 1) : d11430 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1220, d11430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1220, d11430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1221 q = 1) (hb : d85721 q = 1) : d11431 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1221, d11431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d1221, d11431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h19 p ha hb
theorem andIntro15794 (p : Pattern) (ha : d1227 p = 1) (hb : d85721 p = 1) : d11437 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1222 q = 1) (hb : d85721 q = 1) : d11432 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, d11432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15793 q ha hb
    | true =>
      simp only [d1222, d11432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1223 q = 1) (hb : d85721 q = 1) : d11433 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, d11433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1223, d11433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1149 q = 1) (hb : d85721 q = 1) : d11376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d11376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15775 q ha hb
    | true =>
      simp only [d1149, d11376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1150 q = 1) (hb : d85721 q = 1) : d11377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d11377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d11377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1224 q = 1) (hb : d85721 q = 1) : d11434 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1224, d11434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1224, d11434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1225 q = 1) (hb : d85721 q = 1) : d11435 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1225, d11435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1225, d11435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1226 q = 1) (hb : d85721 q = 1) : d11436 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1226, d11436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1226, d11436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1227 q = 1) (hb : d85721 q = 1) : d11437 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1227, d11437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1227, d11437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15795 (p : Pattern) (ha : d5552 p = 1) (hb : d85721 p = 1) : d11470 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1126 q = 1) : d1126 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1128 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1129 q = 1) (hb : d85721 q = 1) : d11366 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1129, d85721, d11366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1129, d85721, d11366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1130 q = 1) (hb : d85721 q = 1) : d11367 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1130, d11367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1130, d11367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1131 q = 1) (hb : d85721 q = 1) : d11368 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1131, d11368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1131, d11368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1128 q = 1) : d1128 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1141 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1142 q = 1) (hb : d85721 q = 1) : d11369 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1142, d85721, d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1142, d85721, d11369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1143 q = 1) (hb : d85721 q = 1) : d11370 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1143, d11370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1143, d11370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1144 q = 1) (hb : d85721 q = 1) : d11371 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1144, d11371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1144, d11371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1145 q = 1) (hb : d85721 q = 1) : d11372 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1145, d11372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1145, d11372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d5545 q = 1) : d5545 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d5546 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d5547 q = 1) (hb : d85721 q = 1) : d11465 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5547, d85721, d11465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d5547, d85721, d11465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d5548 q = 1) (hb : d85721 q = 1) : d11466 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5548, d11466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5548, d11466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d5549 q = 1) (hb : d85721 q = 1) : d11467 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5549, d11467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5549, d11467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5550 q = 1) (hb : d85721 q = 1) : d11468 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5550, d11468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5550, d11468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5551 q = 1) (hb : d85721 q = 1) : d11469 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5551, d11469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5551, d11469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5552 q = 1) (hb : d85721 q = 1) : d11470 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5552, d11470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5552, d11470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h19 p ha hb
theorem andIntro15796 (p : Pattern) (ha : d5558 p = 1) (hb : d85721 p = 1) : d11476 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5553 q = 1) (hb : d85721 q = 1) : d11471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5553, d11471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15795 q ha hb
    | true =>
      simp only [d5553, d11471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5554 q = 1) (hb : d85721 q = 1) : d11472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5554, d11472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5554, d11472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5555 q = 1) (hb : d85721 q = 1) : d11473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5555, d11473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5555, d11473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5556 q = 1) (hb : d85721 q = 1) : d11474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5556, d11474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5556, d11474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5557 q = 1) (hb : d85721 q = 1) : d11475 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5557, d11475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5557, d11475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5558 q = 1) (hb : d85721 q = 1) : d11476 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5558, d11476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5558, d11476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15797 (p : Pattern) (ha : d74690 p = 1) (hb : d85721 p = 1) : d108942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1186 q = 1) (hb : d85721 q = 1) : d11413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d11413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15789 q ha hb
    | true =>
      simp only [d1186, d11413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15790 q ha hb
  have h2 (q : Pattern) (ha : d1187 q = 1) (hb : d85721 q = 1) : d11414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d11414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, d11414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1188 q = 1) (hb : d85721 q = 1) : d11415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d11415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1188, d11415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1189 q = 1) (hb : d85721 q = 1) : d11416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d11416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d11416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1196 q = 1) (hb : d85721 q = 1) : d11423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d11423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15791 q ha hb
    | true =>
      simp only [d1196, d11423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15792 q ha hb
  have h6 (q : Pattern) (ha : d1197 q = 1) (hb : d85721 q = 1) : d11424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d11424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d11424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1198 q = 1) (hb : d85721 q = 1) : d11425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d11425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1198, d11425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1228 q = 1) (hb : d85721 q = 1) : d11438 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d11438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15794 q ha hb
    | true =>
      simp only [d1228, d11438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15777 q ha hb
  have h9 (q : Pattern) (ha : d4485 q = 1) (hb : d85721 q = 1) : d108938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d108938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4485, d108938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5559 q = 1) (hb : d85721 q = 1) : d11477 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5559, d11477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15796 q ha hb
    | true =>
      simp only [d5559, d11477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5560 q = 1) (hb : d85721 q = 1) : d11478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5560, d11478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5560, d11478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74687 q = 1) (hb : d85721 q = 1) : d108939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74687, d108939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74687, d108939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74688 q = 1) (hb : d85721 q = 1) : d108940 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74688, d108940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74688, d108940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74689 q = 1) (hb : d85721 q = 1) : d108941 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74689, d108941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74689, d108941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74690 q = 1) (hb : d85721 q = 1) : d108942 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74690, d108942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74690, d108942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro15798 (p : Pattern) (ha : d1326 p = 1) (hb : d85721 p = 1) : d11483 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d85721 q = 1) : d11376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d11376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15775 q ha hb
    | true =>
      simp only [d1149, d11376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d85721 q = 1) : d11377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d11377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d11377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d85721 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15776 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d85721 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d85721 q = 1) : d11382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d11382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d11382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1156 q = 1) (hb : d85721 q = 1) : d11383 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1156, d11383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1156, d11383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1182 q = 1) (hb : d85721 q = 1) : d11409 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1182, d11409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1182, d11409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1326 q = 1) (hb : d85721 q = 1) : d11483 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1326, d11483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1326, d11483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15799 (p : Pattern) (ha : d1327 p = 1) (hb : d85721 p = 1) : d11484 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d85721 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15776 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d85721 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d85721 q = 1) : d11386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1160 q = 1) (hb : d85721 q = 1) : d11387 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1160, d11387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1184 q = 1) (hb : d85721 q = 1) : d11411 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1184, d11411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1184, d11411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1327 q = 1) (hb : d85721 q = 1) : d11484 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1327, d11484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1327, d11484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15800 (p : Pattern) (ha : d1332 p = 1) (hb : d85721 p = 1) : d11489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1149 q = 1) (hb : d85721 q = 1) : d11376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d11376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15775 q ha hb
    | true =>
      simp only [d1149, d11376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1150 q = 1) (hb : d85721 q = 1) : d11377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d11377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d11377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1153 q = 1) (hb : d85721 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15776 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1154 q = 1) (hb : d85721 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1155 q = 1) (hb : d85721 q = 1) : d11382 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1155, d11382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1155, d11382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1190 q = 1) (hb : d85721 q = 1) : d11417 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1190, d11417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1190, d11417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1191 q = 1) (hb : d85721 q = 1) : d11418 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1191, d11418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1191, d11418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1332 q = 1) (hb : d85721 q = 1) : d11489 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1332, d11489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1332, d11489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15801 (p : Pattern) (ha : d1333 p = 1) (hb : d85721 p = 1) : d11490 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1153 q = 1) (hb : d85721 q = 1) : d11380 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15776 q ha hb
    | true =>
      simp only [d1153, d11380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1154 q = 1) (hb : d85721 q = 1) : d11381 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1154, d11381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1159 q = 1) (hb : d85721 q = 1) : d11386 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1159, d11386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1193 q = 1) (hb : d85721 q = 1) : d11420 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1193, d11420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1193, d11420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1194 q = 1) (hb : d85721 q = 1) : d11421 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1194, d11421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1194, d11421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1333 q = 1) (hb : d85721 q = 1) : d11490 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1333, d11490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1333, d11490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15802 (p : Pattern) (ha : d1337 p = 1) (hb : d85721 p = 1) : d11494 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1222 q = 1) (hb : d85721 q = 1) : d11432 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1222, d11432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15793 q ha hb
    | true =>
      simp only [d1222, d11432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1223 q = 1) (hb : d85721 q = 1) : d11433 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1223, d11433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1223, d11433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1149 q = 1) (hb : d85721 q = 1) : d11376 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1149, d11376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15775 q ha hb
    | true =>
      simp only [d1149, d11376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1150 q = 1) (hb : d85721 q = 1) : d11377 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1150, d11377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1150, d11377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1224 q = 1) (hb : d85721 q = 1) : d11434 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1224, d11434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1224, d11434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1225 q = 1) (hb : d85721 q = 1) : d11435 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1225, d11435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1225, d11435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1226 q = 1) (hb : d85721 q = 1) : d11436 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1226, d11436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1226, d11436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1337 q = 1) (hb : d85721 q = 1) : d11494 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1337, d11494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1337, d11494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15803 (p : Pattern) (ha : d5565 p = 1) (hb : d85721 p = 1) : d11500 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5553 q = 1) (hb : d85721 q = 1) : d11471 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5553, d11471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15795 q ha hb
    | true =>
      simp only [d5553, d11471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5554 q = 1) (hb : d85721 q = 1) : d11472 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5554, d11472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5554, d11472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5555 q = 1) (hb : d85721 q = 1) : d11473 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5555, d11473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5555, d11473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5556 q = 1) (hb : d85721 q = 1) : d11474 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5556, d11474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5556, d11474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5557 q = 1) (hb : d85721 q = 1) : d11475 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5557, d11475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5557, d11475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5565 q = 1) (hb : d85721 q = 1) : d11500 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5565, d11500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5565, d11500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15804 (p : Pattern) (ha : d74694 p = 1) (hb : d85721 p = 1) : d108947 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1186 q = 1) (hb : d85721 q = 1) : d11413 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1186, d11413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15789 q ha hb
    | true =>
      simp only [d1186, d11413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15790 q ha hb
  have h2 (q : Pattern) (ha : d1187 q = 1) (hb : d85721 q = 1) : d11414 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1187, d11414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1187, d11414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1188 q = 1) (hb : d85721 q = 1) : d11415 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1188, d11415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1188, d11415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1189 q = 1) (hb : d85721 q = 1) : d11416 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1189, d11416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1189, d11416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1196 q = 1) (hb : d85721 q = 1) : d11423 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1196, d11423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15791 q ha hb
    | true =>
      simp only [d1196, d11423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15792 q ha hb
  have h6 (q : Pattern) (ha : d1197 q = 1) (hb : d85721 q = 1) : d11424 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1197, d11424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1197, d11424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1198 q = 1) (hb : d85721 q = 1) : d11425 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1198, d11425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1198, d11425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1228 q = 1) (hb : d85721 q = 1) : d11438 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1228, d11438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15794 q ha hb
    | true =>
      simp only [d1228, d11438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15777 q ha hb
  have h9 (q : Pattern) (ha : d4485 q = 1) (hb : d85721 q = 1) : d108938 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4485, d108938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4485, d108938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5559 q = 1) (hb : d85721 q = 1) : d11477 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5559, d11477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15796 q ha hb
    | true =>
      simp only [d5559, d11477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5560 q = 1) (hb : d85721 q = 1) : d11478 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5560, d11478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5560, d11478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74687 q = 1) (hb : d85721 q = 1) : d108939 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74687, d108939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74687, d108939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74688 q = 1) (hb : d85721 q = 1) : d108940 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74688, d108940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74688, d108940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74689 q = 1) (hb : d85721 q = 1) : d108941 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74689, d108941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74689, d108941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1328 q = 1) (hb : d85721 q = 1) : d11485 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1328, d11485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15798 q ha hb
    | true =>
      simp only [d1328, d11485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15799 q ha hb
  have h16 (q : Pattern) (ha : d1329 q = 1) (hb : d85721 q = 1) : d11486 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1329, d11486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1329, d11486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1330 q = 1) (hb : d85721 q = 1) : d11487 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1330, d11487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1330, d11487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d1331 q = 1) (hb : d85721 q = 1) : d11488 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1331, d11488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1331, d11488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1334 q = 1) (hb : d85721 q = 1) : d11491 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1334, d11491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15800 q ha hb
    | true =>
      simp only [d1334, d11491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15801 q ha hb
  have h20 (q : Pattern) (ha : d1335 q = 1) (hb : d85721 q = 1) : d11492 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1335, d11492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1335, d11492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d1336 q = 1) (hb : d85721 q = 1) : d11493 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1336, d11493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d1336, d11493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d1338 q = 1) (hb : d85721 q = 1) : d11495 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d11495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15802 q ha hb
    | true =>
      simp only [d1338, d11495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15780 q ha hb
  have h23 (q : Pattern) (ha : d4490 q = 1) (hb : d85721 q = 1) : d108943 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d108943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4490, d108943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5566 q = 1) (hb : d85721 q = 1) : d11501 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5566, d11501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15803 q ha hb
    | true =>
      simp only [d5566, d11501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5567 q = 1) (hb : d85721 q = 1) : d11502 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5567, d11502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5567, d11502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d74691 q = 1) (hb : d85721 q = 1) : d108944 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74691, d108944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d74691, d108944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d74692 q = 1) (hb : d85721 q = 1) : d108945 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74692, d108945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74692, d108945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d74693 q = 1) (hb : d85721 q = 1) : d108946 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74693, d108946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74693, d108946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d74694 q = 1) (hb : d85721 q = 1) : d108947 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74694, d108947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74694, d108947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro15805 (p : Pattern) (ha : d74701 p = 1) (hb : d85721 p = 1) : d108954 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1338 q = 1) (hb : d85721 q = 1) : d11495 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1338, d11495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15802 q ha hb
    | true =>
      simp only [d1338, d11495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15780 q ha hb
  have h2 (q : Pattern) (ha : d4490 q = 1) (hb : d85721 q = 1) : d108943 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4490, d108943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4490, d108943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5566 q = 1) (hb : d85721 q = 1) : d11501 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5566, d11501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15803 q ha hb
    | true =>
      simp only [d5566, d11501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5567 q = 1) (hb : d85721 q = 1) : d11502 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5567, d11502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5567, d11502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74691 q = 1) (hb : d85721 q = 1) : d108944 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74691, d108944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74691, d108944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74699 q = 1) (hb : d85721 q = 1) : d108952 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74699, d108952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74699, d108952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74700 q = 1) (hb : d85721 q = 1) : d108953 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74700, d108953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74700, d108953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74701 q = 1) (hb : d85721 q = 1) : d108954 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74701, d108954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74701, d108954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15806 (p : Pattern) (ha : d1417 p = 1) (hb : d85721 p = 1) : d11546 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1390 q = 1) : d1390 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1396 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1397 q = 1) (hb : d85721 q = 1) : d11534 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1397, d85721, d11534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1397, d85721, d11534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1398 q = 1) (hb : d85721 q = 1) : d11535 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1398, d11535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1398, d11535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1399 q = 1) (hb : d85721 q = 1) : d11536 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1399, d11536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1399, d11536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1396 q = 1) : d1396 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1401 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1402 q = 1) (hb : d85721 q = 1) : d11537 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d85721, d11537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1402, d85721, d11537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1403 q = 1) (hb : d85721 q = 1) : d11538 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d11538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d11538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1404 q = 1) (hb : d85721 q = 1) : d11539 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d11539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d11539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1405 q = 1) (hb : d85721 q = 1) : d11540 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1405, d11540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1405, d11540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d1401 q = 1) : d1401 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d1411 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1412 q = 1) (hb : d85721 q = 1) : d11541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d85721, d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1412, d85721, d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d1413 q = 1) (hb : d85721 q = 1) : d11542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d11542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d11542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1414 q = 1) (hb : d85721 q = 1) : d11543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d11543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d11543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1415 q = 1) (hb : d85721 q = 1) : d11544 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d11544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1415, d11544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1416 q = 1) (hb : d85721 q = 1) : d11545 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1416, d11545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1416, d11545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1417 q = 1) (hb : d85721 q = 1) : d11546 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1417, d11546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d1417, d11546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h19 p ha hb
theorem andIntro15807 (p : Pattern) (ha : d1422 p = 1) (hb : d85721 p = 1) : d11551 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1396 q = 1) : d1396 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1401 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1402 q = 1) (hb : d85721 q = 1) : d11537 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d85721, d11537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1402, d85721, d11537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1403 q = 1) (hb : d85721 q = 1) : d11538 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d11538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d11538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1404 q = 1) (hb : d85721 q = 1) : d11539 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d11539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d11539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1401 q = 1) : d1401 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1411 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1412 q = 1) (hb : d85721 q = 1) : d11541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d85721, d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1412, d85721, d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1413 q = 1) (hb : d85721 q = 1) : d11542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d11542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d11542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1414 q = 1) (hb : d85721 q = 1) : d11543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d11543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d11543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1415 q = 1) (hb : d85721 q = 1) : d11544 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d11544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1415, d11544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1420 q = 1) (hb : d85721 q = 1) : d11549 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1420, d11549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1420, d11549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1421 q = 1) (hb : d85721 q = 1) : d11550 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1421, d11550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1421, d11550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1422 q = 1) (hb : d85721 q = 1) : d11551 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1422, d11551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1422, d11551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro15808 (p : Pattern) (ha : d1428 p = 1) (hb : d85721 p = 1) : d11557 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1418 q = 1) (hb : d85721 q = 1) : d11547 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1418, d11547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15806 q ha hb
    | true =>
      simp only [d1418, d11547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1419 q = 1) (hb : d85721 q = 1) : d11548 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1419, d11548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1419, d11548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1423 q = 1) (hb : d85721 q = 1) : d11552 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1423, d11552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15807 q ha hb
    | true =>
      simp only [d1423, d11552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1424 q = 1) (hb : d85721 q = 1) : d11553 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1424, d11553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1424, d11553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1425 q = 1) (hb : d85721 q = 1) : d11554 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1425, d11554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1425, d11554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1426 q = 1) (hb : d85721 q = 1) : d11555 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1426, d11555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1426, d11555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1427 q = 1) (hb : d85721 q = 1) : d11556 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1427, d11556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1427, d11556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1428 q = 1) (hb : d85721 q = 1) : d11557 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1428, d11557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1428, d11557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15809 (p : Pattern) (ha : d1436 p = 1) (hb : d85721 p = 1) : d11565 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1423 q = 1) (hb : d85721 q = 1) : d11552 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1423, d11552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15807 q ha hb
    | true =>
      simp only [d1423, d11552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1424 q = 1) (hb : d85721 q = 1) : d11553 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1424, d11553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1424, d11553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1431 q = 1) (hb : d85721 q = 1) : d11560 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1431, d11560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15786 q ha hb
    | true =>
      simp only [d1431, d11560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1432 q = 1) (hb : d85721 q = 1) : d11561 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1432, d11561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1432, d11561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1433 q = 1) (hb : d85721 q = 1) : d11562 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1433, d11562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1433, d11562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1434 q = 1) (hb : d85721 q = 1) : d11563 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1434, d11563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1434, d11563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1435 q = 1) (hb : d85721 q = 1) : d11564 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1435, d11564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1435, d11564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1436 q = 1) (hb : d85721 q = 1) : d11565 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1436, d11565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1436, d11565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15810 (p : Pattern) (ha : d5596 p = 1) (hb : d85721 p = 1) : d11598 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1396 q = 1) : d1396 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1401 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1402 q = 1) (hb : d85721 q = 1) : d11537 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1402, d85721, d11537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1402, d85721, d11537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1403 q = 1) (hb : d85721 q = 1) : d11538 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1403, d11538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1403, d11538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1404 q = 1) (hb : d85721 q = 1) : d11539 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1404, d11539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1404, d11539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1401 q = 1) : d1401 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1411 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1412 q = 1) (hb : d85721 q = 1) : d11541 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1412, d85721, d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1412, d85721, d11541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1413 q = 1) (hb : d85721 q = 1) : d11542 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1413, d11542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1413, d11542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1414 q = 1) (hb : d85721 q = 1) : d11543 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1414, d11543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1414, d11543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1415 q = 1) (hb : d85721 q = 1) : d11544 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1415, d11544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1415, d11544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d5589 q = 1) : d5589 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d5590 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d5591 q = 1) (hb : d85721 q = 1) : d11593 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5591, d85721, d11593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d5591, d85721, d11593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d5592 q = 1) (hb : d85721 q = 1) : d11594 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5592, d11594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5592, d11594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d5593 q = 1) (hb : d85721 q = 1) : d11595 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5593, d11595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5593, d11595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5594 q = 1) (hb : d85721 q = 1) : d11596 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5594, d11596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5594, d11596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5595 q = 1) (hb : d85721 q = 1) : d11597 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5595, d11597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5595, d11597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5596 q = 1) (hb : d85721 q = 1) : d11598 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5596, d11598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5596, d11598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h19 p ha hb
theorem andIntro15811 (p : Pattern) (ha : d5602 p = 1) (hb : d85721 p = 1) : d11604 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5597 q = 1) (hb : d85721 q = 1) : d11599 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5597, d11599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15810 q ha hb
    | true =>
      simp only [d5597, d11599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5598 q = 1) (hb : d85721 q = 1) : d11600 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5598, d11600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5598, d11600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5599 q = 1) (hb : d85721 q = 1) : d11601 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5599, d11601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5599, d11601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5600 q = 1) (hb : d85721 q = 1) : d11602 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5600, d11602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5600, d11602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5601 q = 1) (hb : d85721 q = 1) : d11603 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5601, d11603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5601, d11603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5602 q = 1) (hb : d85721 q = 1) : d11604 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5602, d11604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5602, d11604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15812 (p : Pattern) (ha : d74710 p = 1) (hb : d85721 p = 1) : d108964 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1437 q = 1) (hb : d85721 q = 1) : d11566 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1437, d11566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15808 q ha hb
    | true =>
      simp only [d1437, d11566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15809 q ha hb
  have h2 (q : Pattern) (ha : d4505 q = 1) (hb : d85721 q = 1) : d108960 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4505, d108960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4505, d108960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5603 q = 1) (hb : d85721 q = 1) : d11605 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5603, d11605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15811 q ha hb
    | true =>
      simp only [d5603, d11605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5604 q = 1) (hb : d85721 q = 1) : d11606 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5604, d11606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5604, d11606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74707 q = 1) (hb : d85721 q = 1) : d108961 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74707, d108961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74707, d108961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74708 q = 1) (hb : d85721 q = 1) : d108962 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74708, d108962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74708, d108962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74709 q = 1) (hb : d85721 q = 1) : d108963 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74709, d108963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74709, d108963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74710 q = 1) (hb : d85721 q = 1) : d108964 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74710, d108964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74710, d108964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15813 (p : Pattern) (ha : d74716 p = 1) (hb : d85721 p = 1) : d108970 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1169 q = 1) (hb : d85721 q = 1) : d11396 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d11396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1169, d11396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15779 q ha hb
  have h2 (q : Pattern) (ha : d1170 q = 1) (hb : d85721 q = 1) : d11397 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d11397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1170, d11397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1179 q = 1) (hb : d85721 q = 1) : d11406 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d11406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15779 q ha hb
    | true =>
      simp only [d1179, d11406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15782 q ha hb
  have h4 (q : Pattern) (ha : d1180 q = 1) (hb : d85721 q = 1) : d11407 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d11407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1180, d11407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1181 q = 1) (hb : d85721 q = 1) : d11408 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d11408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1181, d11408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74695 q = 1) (hb : d85721 q = 1) : d108948 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74695, d108948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15797 q ha hb
    | true =>
      simp only [d74695, d108948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15804 q ha hb
  have h7 (q : Pattern) (ha : d1362 q = 1) (hb : d85721 q = 1) : d11520 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, d11520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15783 q ha hb
    | true =>
      simp only [d1362, d11520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15784 q ha hb
  have h8 (q : Pattern) (ha : d74696 q = 1) (hb : d85721 q = 1) : d108949 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74696, d108949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74696, d108949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74697 q = 1) (hb : d85721 q = 1) : d108950 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74697, d108950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74697, d108950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d74698 q = 1) (hb : d85721 q = 1) : d108951 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74698, d108951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74698, d108951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74702 q = 1) (hb : d85721 q = 1) : d108955 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74702, d108955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74702, d108955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15805 q ha hb
  have h12 (q : Pattern) (ha : d1371 q = 1) (hb : d85721 q = 1) : d11529 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d11529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1371, d11529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15785 q ha hb
  have h13 (q : Pattern) (ha : d74703 q = 1) (hb : d85721 q = 1) : d108956 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74703, d108956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74703, d108956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74704 q = 1) (hb : d85721 q = 1) : d108957 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74704, d108957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74704, d108957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d74705 q = 1) (hb : d85721 q = 1) : d108958 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74705, d108958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74705, d108958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d74706 q = 1) (hb : d85721 q = 1) : d108959 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74706, d108959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74706, d108959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74711 q = 1) (hb : d85721 q = 1) : d108965 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74711, d108965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74711, d108965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15812 q ha hb
  have h18 (q : Pattern) (ha : d1504 q = 1) (hb : d85721 q = 1) : d11622 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1504, d11622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1504, d11622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15788 q ha hb
  have h19 (q : Pattern) (ha : d74712 q = 1) (hb : d85721 q = 1) : d108966 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74712, d108966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74712, d108966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d74713 q = 1) (hb : d85721 q = 1) : d108967 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74713, d108967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74713, d108967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d74714 q = 1) (hb : d85721 q = 1) : d108968 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74714, d108968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74714, d108968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d74715 q = 1) (hb : d85721 q = 1) : d108969 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74715, d108969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74715, d108969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d74716 q = 1) (hb : d85721 q = 1) : d108970 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74716, d108970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74716, d108970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro15814 (p : Pattern) (ha : d74722 p = 1) (hb : d85721 p = 1) : d108976 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74717 q = 1) (hb : d85721 q = 1) : d108971 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74717, d108971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74717, d108971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15813 q ha hb
  have h2 (q : Pattern) (ha : d74718 q = 1) (hb : d85721 q = 1) : d108972 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74718, d108972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74718, d108972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74719 q = 1) (hb : d85721 q = 1) : d108973 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74719, d108973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74719, d108973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74720 q = 1) (hb : d85721 q = 1) : d108974 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74720, d108974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74720, d108974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74721 q = 1) (hb : d85721 q = 1) : d108975 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74721, d108975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74721, d108975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74722 q = 1) (hb : d85721 q = 1) : d108976 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74722, d108976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74722, d108976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15815 (p : Pattern) (ha : d1609 p = 1) (hb : d85721 p = 1) : d11646 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1587 q = 1) : d1587 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1589 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1590 q = 1) (hb : d85721 q = 1) : d11637 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d85721, d11637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1590, d85721, d11637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1591 q = 1) (hb : d85721 q = 1) : d11638 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d11638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d11638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1592 q = 1) (hb : d85721 q = 1) : d11639 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d11639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d11639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1589 q = 1) : d1589 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1602 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1603 q = 1) (hb : d85721 q = 1) : d11640 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d85721, d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1603, d85721, d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1604 q = 1) (hb : d85721 q = 1) : d11641 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d11641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d11641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1605 q = 1) (hb : d85721 q = 1) : d11642 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d11642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d11642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1606 q = 1) (hb : d85721 q = 1) : d11643 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d11643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1606, d11643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1607 q = 1) (hb : d85721 q = 1) : d11644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, d11644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1607, d11644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1608 q = 1) (hb : d85721 q = 1) : d11645 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1608, d11645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1608, d11645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1609 q = 1) (hb : d85721 q = 1) : d11646 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1609, d11646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1609, d11646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro15816 (p : Pattern) (ha : d1613 p = 1) (hb : d85721 p = 1) : d11650 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1589 q = 1) : d1589 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1602 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1603 q = 1) (hb : d85721 q = 1) : d11640 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d85721, d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1603, d85721, d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1604 q = 1) (hb : d85721 q = 1) : d11641 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d11641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d11641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1605 q = 1) (hb : d85721 q = 1) : d11642 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d11642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d11642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1607 q = 1) (hb : d85721 q = 1) : d11644 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1607, d11644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1607, d11644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1612 q = 1) (hb : d85721 q = 1) : d11649 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1612, d11649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1612, d11649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1613 q = 1) (hb : d85721 q = 1) : d11650 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1613, d11650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1613, d11650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15817 (p : Pattern) (ha : d1619 p = 1) (hb : d85721 p = 1) : d11656 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d85721 q = 1) : d11647 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d11647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15815 q ha hb
    | true =>
      simp only [d1610, d11647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d85721 q = 1) : d11648 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d11648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d11648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d85721 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15816 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d85721 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d85721 q = 1) : d11653 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d11653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d11653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d85721 q = 1) : d11654 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d11654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d11654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1618 q = 1) (hb : d85721 q = 1) : d11655 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1618, d11655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1618, d11655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1619 q = 1) (hb : d85721 q = 1) : d11656 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1619, d11656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1619, d11656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15818 (p : Pattern) (ha : d1623 p = 1) (hb : d85721 p = 1) : d11660 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d85721 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15816 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d85721 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d85721 q = 1) : d11657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d85721 q = 1) : d11658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d85721 q = 1) : d11659 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, d11659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, d11659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1623 q = 1) (hb : d85721 q = 1) : d11660 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1623, d11660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1623, d11660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15819 (p : Pattern) (ha : d1629 p = 1) (hb : d85721 p = 1) : d11666 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1624 q = 1) (hb : d85721 q = 1) : d11661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d11661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15817 q ha hb
    | true =>
      simp only [d1624, d11661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15818 q ha hb
  have h2 (q : Pattern) (ha : d1625 q = 1) (hb : d85721 q = 1) : d11662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d11662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d11662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1626 q = 1) (hb : d85721 q = 1) : d11663 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d11663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1626, d11663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1627 q = 1) (hb : d85721 q = 1) : d11664 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d11664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d11664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1628 q = 1) (hb : d85721 q = 1) : d11665 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d11665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d11665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1629 q = 1) (hb : d85721 q = 1) : d11666 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1629, d11666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1629, d11666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15820 (p : Pattern) (ha : d1632 p = 1) (hb : d85721 p = 1) : d11669 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d85721 q = 1) : d11647 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d11647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15815 q ha hb
    | true =>
      simp only [d1610, d11647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d85721 q = 1) : d11648 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d11648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d11648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d85721 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15816 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d85721 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d85721 q = 1) : d11653 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d11653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d11653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d85721 q = 1) : d11654 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d11654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d11654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1618 q = 1) (hb : d85721 q = 1) : d11655 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1618, d11655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1618, d11655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1632 q = 1) (hb : d85721 q = 1) : d11669 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1632, d11669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1632, d11669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15821 (p : Pattern) (ha : d1633 p = 1) (hb : d85721 p = 1) : d11670 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d85721 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15816 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d85721 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d85721 q = 1) : d11657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d85721 q = 1) : d11658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1622 q = 1) (hb : d85721 q = 1) : d11659 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1622, d11659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1622, d11659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1633 q = 1) (hb : d85721 q = 1) : d11670 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1633, d11670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1633, d11670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15822 (p : Pattern) (ha : d1639 p = 1) (hb : d85721 p = 1) : d11676 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1624 q = 1) (hb : d85721 q = 1) : d11661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d11661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15817 q ha hb
    | true =>
      simp only [d1624, d11661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15818 q ha hb
  have h2 (q : Pattern) (ha : d1625 q = 1) (hb : d85721 q = 1) : d11662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d11662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d11662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1626 q = 1) (hb : d85721 q = 1) : d11663 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d11663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1626, d11663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1627 q = 1) (hb : d85721 q = 1) : d11664 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d11664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d11664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1628 q = 1) (hb : d85721 q = 1) : d11665 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d11665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d11665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1634 q = 1) (hb : d85721 q = 1) : d11671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1634, d11671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15820 q ha hb
    | true =>
      simp only [d1634, d11671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15821 q ha hb
  have h7 (q : Pattern) (ha : d1635 q = 1) (hb : d85721 q = 1) : d11672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1635, d11672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1635, d11672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1636 q = 1) (hb : d85721 q = 1) : d11673 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1636, d11673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1636, d11673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1637 q = 1) (hb : d85721 q = 1) : d11674 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1637, d11674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1637, d11674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1638 q = 1) (hb : d85721 q = 1) : d11675 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1638, d11675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1638, d11675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1639 q = 1) (hb : d85721 q = 1) : d11676 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1639, d11676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1639, d11676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15823 (p : Pattern) (ha : d1832 p = 1) (hb : d85721 p = 1) : d11784 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1624 q = 1) (hb : d85721 q = 1) : d11661 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1624, d11661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15817 q ha hb
    | true =>
      simp only [d1624, d11661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15818 q ha hb
  have h2 (q : Pattern) (ha : d1625 q = 1) (hb : d85721 q = 1) : d11662 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1625, d11662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1625, d11662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1626 q = 1) (hb : d85721 q = 1) : d11663 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1626, d11663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1626, d11663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1627 q = 1) (hb : d85721 q = 1) : d11664 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1627, d11664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1627, d11664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1628 q = 1) (hb : d85721 q = 1) : d11665 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1628, d11665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1628, d11665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1827 q = 1) (hb : d85721 q = 1) : d11779 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d11779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15818 q ha hb
    | true =>
      simp only [d1827, d11779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1828 q = 1) (hb : d85721 q = 1) : d11780 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d11780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d11780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1829 q = 1) (hb : d85721 q = 1) : d11781 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d11781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1829, d11781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1830 q = 1) (hb : d85721 q = 1) : d11782 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d11782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d11782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1831 q = 1) (hb : d85721 q = 1) : d11783 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d11783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d11783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1832 q = 1) (hb : d85721 q = 1) : d11784 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1832, d11784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1832, d11784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15824 (p : Pattern) (ha : d1838 p = 1) (hb : d85721 p = 1) : d11790 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1827 q = 1) (hb : d85721 q = 1) : d11779 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1827, d11779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15818 q ha hb
    | true =>
      simp only [d1827, d11779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1828 q = 1) (hb : d85721 q = 1) : d11780 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1828, d11780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1828, d11780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1829 q = 1) (hb : d85721 q = 1) : d11781 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1829, d11781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1829, d11781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1830 q = 1) (hb : d85721 q = 1) : d11782 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1830, d11782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1830, d11782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1831 q = 1) (hb : d85721 q = 1) : d11783 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1831, d11783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1831, d11783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1833 q = 1) (hb : d85721 q = 1) : d11785 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d11785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15821 q ha hb
    | true =>
      simp only [d1833, d11785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1834 q = 1) (hb : d85721 q = 1) : d11786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d11786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, d11786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1835 q = 1) (hb : d85721 q = 1) : d11787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d11787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1835, d11787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d1836 q = 1) (hb : d85721 q = 1) : d11788 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d11788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, d11788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1837 q = 1) (hb : d85721 q = 1) : d11789 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d11789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, d11789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1838 q = 1) (hb : d85721 q = 1) : d11790 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1838, d11790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1838, d11790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15825 (p : Pattern) (ha : d1847 p = 1) (hb : d85721 p = 1) : d11799 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1833 q = 1) (hb : d85721 q = 1) : d11785 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1833, d11785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15821 q ha hb
    | true =>
      simp only [d1833, d11785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1834 q = 1) (hb : d85721 q = 1) : d11786 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1834, d11786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1834, d11786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1835 q = 1) (hb : d85721 q = 1) : d11787 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1835, d11787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1835, d11787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1836 q = 1) (hb : d85721 q = 1) : d11788 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1836, d11788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1836, d11788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1837 q = 1) (hb : d85721 q = 1) : d11789 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1837, d11789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1837, d11789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1847 q = 1) (hb : d85721 q = 1) : d11799 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1847, d11799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1847, d11799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15826 (p : Pattern) (ha : d1907 p = 1) (hb : d85721 p = 1) : d11830 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1878 q = 1) : d1878 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1888 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1889 q = 1) (hb : d85721 q = 1) : d11812 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d85721, d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1889, d85721, d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1890 q = 1) (hb : d85721 q = 1) : d11813 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d11813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d11813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1891 q = 1) (hb : d85721 q = 1) : d11814 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d11814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d11814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1897 q = 1) (hb : d85721 q = 1) : d11820 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d11820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1897, d11820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1906 q = 1) (hb : d85721 q = 1) : d11829 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1906, d11829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1906, d11829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1907 q = 1) (hb : d85721 q = 1) : d11830 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1907, d11830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1907, d11830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15827 (p : Pattern) (ha : d1974 p = 1) (hb : d85721 p = 1) : d11886 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1908 q = 1) (hb : d85721 q = 1) : d11831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d11831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15826 q ha hb
    | true =>
      simp only [d1908, d11831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1909 q = 1) (hb : d85721 q = 1) : d11832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d11832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d11832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1971 q = 1) (hb : d85721 q = 1) : d11883 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1971, d11883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1971, d11883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1972 q = 1) (hb : d85721 q = 1) : d11884 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1972, d11884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1972, d11884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1973 q = 1) (hb : d85721 q = 1) : d11885 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1973, d11885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1973, d11885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1974 q = 1) (hb : d85721 q = 1) : d11886 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1974, d11886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1974, d11886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15828 (p : Pattern) (ha : d1980 p = 1) (hb : d85721 p = 1) : d11892 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1975 q = 1) (hb : d85721 q = 1) : d11887 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1975, d11887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15827 q ha hb
    | true =>
      simp only [d1975, d11887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1976 q = 1) (hb : d85721 q = 1) : d11888 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1976, d11888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1976, d11888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1977 q = 1) (hb : d85721 q = 1) : d11889 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1977, d11889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1977, d11889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1978 q = 1) (hb : d85721 q = 1) : d11890 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1978, d11890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1978, d11890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1979 q = 1) (hb : d85721 q = 1) : d11891 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d1979, d11891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1979, d11891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1980 q = 1) (hb : d85721 q = 1) : d11892 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d1980, d11892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1980, d11892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15829 (p : Pattern) (ha : d1644 p = 1) (hb : d85721 p = 1) : d11681 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d85721 q = 1) : d11647 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d11647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15815 q ha hb
    | true =>
      simp only [d1610, d11647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d85721 q = 1) : d11648 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d11648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d11648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d85721 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15816 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d85721 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d85721 q = 1) : d11653 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d11653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d11653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d85721 q = 1) : d11654 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d11654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d11654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1643 q = 1) (hb : d85721 q = 1) : d11680 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1643, d11680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1643, d11680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1644 q = 1) (hb : d85721 q = 1) : d11681 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1644, d11681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1644, d11681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15830 (p : Pattern) (ha : d1646 p = 1) (hb : d85721 p = 1) : d11683 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d85721 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15816 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d85721 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d85721 q = 1) : d11657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d85721 q = 1) : d11658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1645 q = 1) (hb : d85721 q = 1) : d11682 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d11682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, d11682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1646 q = 1) (hb : d85721 q = 1) : d11683 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1646, d11683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1646, d11683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15831 (p : Pattern) (ha : d1653 p = 1) (hb : d85721 p = 1) : d11690 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d85721 q = 1) : d11647 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d11647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15815 q ha hb
    | true =>
      simp only [d1610, d11647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d85721 q = 1) : d11648 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d11648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d11648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d85721 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15816 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d85721 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d85721 q = 1) : d11653 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d11653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d11653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1651 q = 1) (hb : d85721 q = 1) : d11688 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1651, d11688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1651, d11688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1652 q = 1) (hb : d85721 q = 1) : d11689 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1652, d11689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1652, d11689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1653 q = 1) (hb : d85721 q = 1) : d11690 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1653, d11690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1653, d11690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15832 (p : Pattern) (ha : d1656 p = 1) (hb : d85721 p = 1) : d11693 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d85721 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15816 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d85721 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d85721 q = 1) : d11657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1654 q = 1) (hb : d85721 q = 1) : d11691 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d11691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, d11691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1655 q = 1) (hb : d85721 q = 1) : d11692 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, d11692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1655, d11692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1656 q = 1) (hb : d85721 q = 1) : d11693 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1656, d11693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1656, d11693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15833 (p : Pattern) (ha : d1676 p = 1) (hb : d85721 p = 1) : d11702 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1670 q = 1) : d1670 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1587 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1671 q = 1) (hb : d85721 q = 1) : d11697 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1671, d85721, d11697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1671, d85721, d11697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1672 q = 1) (hb : d85721 q = 1) : d11698 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1672, d11698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1672, d11698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1673 q = 1) (hb : d85721 q = 1) : d11699 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1673, d11699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1673, d11699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1587 q = 1) : d1587 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1589 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1590 q = 1) (hb : d85721 q = 1) : d11637 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d85721, d11637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1590, d85721, d11637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1591 q = 1) (hb : d85721 q = 1) : d11638 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d11638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d11638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1592 q = 1) (hb : d85721 q = 1) : d11639 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d11639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d11639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1674 q = 1) (hb : d85721 q = 1) : d11700 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1674, d11700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1674, d11700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d1589 q = 1) : d1589 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d1602 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1603 q = 1) (hb : d85721 q = 1) : d11640 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d85721, d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1603, d85721, d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d1604 q = 1) (hb : d85721 q = 1) : d11641 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d11641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d11641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1605 q = 1) (hb : d85721 q = 1) : d11642 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d11642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d11642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1606 q = 1) (hb : d85721 q = 1) : d11643 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d11643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1606, d11643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1675 q = 1) (hb : d85721 q = 1) : d11701 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1675, d11701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1675, d11701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1676 q = 1) (hb : d85721 q = 1) : d11702 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1676, d11702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d1676, d11702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h19 p ha hb
theorem andIntro15834 (p : Pattern) (ha : d1682 p = 1) (hb : d85721 p = 1) : d11708 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1677 q = 1) (hb : d85721 q = 1) : d11703 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, d11703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15833 q ha hb
    | true =>
      simp only [d1677, d11703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1678 q = 1) (hb : d85721 q = 1) : d11704 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, d11704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1678, d11704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1610 q = 1) (hb : d85721 q = 1) : d11647 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d11647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15815 q ha hb
    | true =>
      simp only [d1610, d11647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1611 q = 1) (hb : d85721 q = 1) : d11648 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d11648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d11648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1679 q = 1) (hb : d85721 q = 1) : d11705 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1679, d11705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1679, d11705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1680 q = 1) (hb : d85721 q = 1) : d11706 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1680, d11706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1680, d11706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1681 q = 1) (hb : d85721 q = 1) : d11707 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1681, d11707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1681, d11707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1682 q = 1) (hb : d85721 q = 1) : d11708 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1682, d11708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1682, d11708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15835 (p : Pattern) (ha : d5642 p = 1) (hb : d85721 p = 1) : d11741 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1587 q = 1) : d1587 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1589 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1590 q = 1) (hb : d85721 q = 1) : d11637 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1590, d85721, d11637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1590, d85721, d11637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1591 q = 1) (hb : d85721 q = 1) : d11638 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1591, d11638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1591, d11638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1592 q = 1) (hb : d85721 q = 1) : d11639 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1592, d11639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1592, d11639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1589 q = 1) : d1589 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1602 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1603 q = 1) (hb : d85721 q = 1) : d11640 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1603, d85721, d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1603, d85721, d11640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1604 q = 1) (hb : d85721 q = 1) : d11641 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1604, d11641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1604, d11641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1605 q = 1) (hb : d85721 q = 1) : d11642 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1605, d11642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1605, d11642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1606 q = 1) (hb : d85721 q = 1) : d11643 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1606, d11643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1606, d11643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d5635 q = 1) : d5635 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d5636 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d5637 q = 1) (hb : d85721 q = 1) : d11736 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5637, d85721, d11736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d5637, d85721, d11736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d5638 q = 1) (hb : d85721 q = 1) : d11737 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5638, d11737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5638, d11737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d5639 q = 1) (hb : d85721 q = 1) : d11738 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5639, d11738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5639, d11738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5640 q = 1) (hb : d85721 q = 1) : d11739 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5640, d11739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5640, d11739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5641 q = 1) (hb : d85721 q = 1) : d11740 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5641, d11740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5641, d11740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5642 q = 1) (hb : d85721 q = 1) : d11741 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5642, d11741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5642, d11741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h19 p ha hb
theorem andIntro15836 (p : Pattern) (ha : d5648 p = 1) (hb : d85721 p = 1) : d11747 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5643 q = 1) (hb : d85721 q = 1) : d11742 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5643, d11742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15835 q ha hb
    | true =>
      simp only [d5643, d11742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5644 q = 1) (hb : d85721 q = 1) : d11743 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5644, d11743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5644, d11743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5645 q = 1) (hb : d85721 q = 1) : d11744 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5645, d11744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5645, d11744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5646 q = 1) (hb : d85721 q = 1) : d11745 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5646, d11745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5646, d11745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5647 q = 1) (hb : d85721 q = 1) : d11746 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5647, d11746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5647, d11746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5648 q = 1) (hb : d85721 q = 1) : d11747 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5648, d11747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5648, d11747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15837 (p : Pattern) (ha : d74729 p = 1) (hb : d85721 p = 1) : d108984 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1647 q = 1) (hb : d85721 q = 1) : d11684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d11684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15829 q ha hb
    | true =>
      simp only [d1647, d11684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15830 q ha hb
  have h2 (q : Pattern) (ha : d1648 q = 1) (hb : d85721 q = 1) : d11685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d11685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, d11685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1649 q = 1) (hb : d85721 q = 1) : d11686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d11686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1649, d11686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1650 q = 1) (hb : d85721 q = 1) : d11687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d11687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d11687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1657 q = 1) (hb : d85721 q = 1) : d11694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d11694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15831 q ha hb
    | true =>
      simp only [d1657, d11694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15832 q ha hb
  have h6 (q : Pattern) (ha : d1658 q = 1) (hb : d85721 q = 1) : d11695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d11695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d11695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1659 q = 1) (hb : d85721 q = 1) : d11696 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d11696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1659, d11696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1683 q = 1) (hb : d85721 q = 1) : d11709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d11709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15834 q ha hb
    | true =>
      simp only [d1683, d11709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15817 q ha hb
  have h9 (q : Pattern) (ha : d4525 q = 1) (hb : d85721 q = 1) : d108980 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d108980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4525, d108980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5649 q = 1) (hb : d85721 q = 1) : d11748 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5649, d11748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15836 q ha hb
    | true =>
      simp only [d5649, d11748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5650 q = 1) (hb : d85721 q = 1) : d11749 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5650, d11749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5650, d11749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74726 q = 1) (hb : d85721 q = 1) : d108981 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74726, d108981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74726, d108981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74727 q = 1) (hb : d85721 q = 1) : d108982 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74727, d108982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74727, d108982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74728 q = 1) (hb : d85721 q = 1) : d108983 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74728, d108983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74728, d108983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74729 q = 1) (hb : d85721 q = 1) : d108984 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74729, d108984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74729, d108984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro15838 (p : Pattern) (ha : d1803 p = 1) (hb : d85721 p = 1) : d11754 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d85721 q = 1) : d11647 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d11647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15815 q ha hb
    | true =>
      simp only [d1610, d11647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d85721 q = 1) : d11648 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d11648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d11648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d85721 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15816 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d85721 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d85721 q = 1) : d11653 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d11653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d11653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1617 q = 1) (hb : d85721 q = 1) : d11654 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1617, d11654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1617, d11654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1643 q = 1) (hb : d85721 q = 1) : d11680 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1643, d11680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1643, d11680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1803 q = 1) (hb : d85721 q = 1) : d11754 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1803, d11754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1803, d11754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15839 (p : Pattern) (ha : d1804 p = 1) (hb : d85721 p = 1) : d11755 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d85721 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15816 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d85721 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d85721 q = 1) : d11657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1621 q = 1) (hb : d85721 q = 1) : d11658 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1621, d11658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1645 q = 1) (hb : d85721 q = 1) : d11682 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1645, d11682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1645, d11682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1804 q = 1) (hb : d85721 q = 1) : d11755 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1804, d11755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1804, d11755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15840 (p : Pattern) (ha : d1809 p = 1) (hb : d85721 p = 1) : d11760 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1610 q = 1) (hb : d85721 q = 1) : d11647 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d11647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15815 q ha hb
    | true =>
      simp only [d1610, d11647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1611 q = 1) (hb : d85721 q = 1) : d11648 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d11648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d11648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1614 q = 1) (hb : d85721 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15816 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1615 q = 1) (hb : d85721 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1616 q = 1) (hb : d85721 q = 1) : d11653 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1616, d11653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1616, d11653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1651 q = 1) (hb : d85721 q = 1) : d11688 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1651, d11688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1651, d11688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1652 q = 1) (hb : d85721 q = 1) : d11689 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1652, d11689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1652, d11689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1809 q = 1) (hb : d85721 q = 1) : d11760 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1809, d11760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1809, d11760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15841 (p : Pattern) (ha : d1810 p = 1) (hb : d85721 p = 1) : d11761 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1614 q = 1) (hb : d85721 q = 1) : d11651 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15816 q ha hb
    | true =>
      simp only [d1614, d11651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1615 q = 1) (hb : d85721 q = 1) : d11652 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1615, d11652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1620 q = 1) (hb : d85721 q = 1) : d11657 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1620, d11657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1654 q = 1) (hb : d85721 q = 1) : d11691 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1654, d11691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1654, d11691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1655 q = 1) (hb : d85721 q = 1) : d11692 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1655, d11692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1655, d11692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d1810 q = 1) (hb : d85721 q = 1) : d11761 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1810, d11761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1810, d11761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15842 (p : Pattern) (ha : d1814 p = 1) (hb : d85721 p = 1) : d11765 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1677 q = 1) (hb : d85721 q = 1) : d11703 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1677, d11703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15833 q ha hb
    | true =>
      simp only [d1677, d11703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1678 q = 1) (hb : d85721 q = 1) : d11704 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1678, d11704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1678, d11704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1610 q = 1) (hb : d85721 q = 1) : d11647 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1610, d11647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15815 q ha hb
    | true =>
      simp only [d1610, d11647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1611 q = 1) (hb : d85721 q = 1) : d11648 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1611, d11648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1611, d11648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1679 q = 1) (hb : d85721 q = 1) : d11705 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1679, d11705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1679, d11705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1680 q = 1) (hb : d85721 q = 1) : d11706 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1680, d11706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1680, d11706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1681 q = 1) (hb : d85721 q = 1) : d11707 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1681, d11707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1681, d11707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1814 q = 1) (hb : d85721 q = 1) : d11765 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1814, d11765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1814, d11765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15843 (p : Pattern) (ha : d5655 p = 1) (hb : d85721 p = 1) : d11771 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5643 q = 1) (hb : d85721 q = 1) : d11742 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5643, d11742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15835 q ha hb
    | true =>
      simp only [d5643, d11742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5644 q = 1) (hb : d85721 q = 1) : d11743 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5644, d11743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5644, d11743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5645 q = 1) (hb : d85721 q = 1) : d11744 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5645, d11744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5645, d11744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5646 q = 1) (hb : d85721 q = 1) : d11745 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5646, d11745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5646, d11745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5647 q = 1) (hb : d85721 q = 1) : d11746 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5647, d11746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5647, d11746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5655 q = 1) (hb : d85721 q = 1) : d11771 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5655, d11771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5655, d11771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15844 (p : Pattern) (ha : d74733 p = 1) (hb : d85721 p = 1) : d108989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1647 q = 1) (hb : d85721 q = 1) : d11684 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1647, d11684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15829 q ha hb
    | true =>
      simp only [d1647, d11684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15830 q ha hb
  have h2 (q : Pattern) (ha : d1648 q = 1) (hb : d85721 q = 1) : d11685 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1648, d11685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1648, d11685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1649 q = 1) (hb : d85721 q = 1) : d11686 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1649, d11686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1649, d11686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1650 q = 1) (hb : d85721 q = 1) : d11687 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1650, d11687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1650, d11687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1657 q = 1) (hb : d85721 q = 1) : d11694 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1657, d11694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15831 q ha hb
    | true =>
      simp only [d1657, d11694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15832 q ha hb
  have h6 (q : Pattern) (ha : d1658 q = 1) (hb : d85721 q = 1) : d11695 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1658, d11695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1658, d11695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1659 q = 1) (hb : d85721 q = 1) : d11696 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1659, d11696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1659, d11696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1683 q = 1) (hb : d85721 q = 1) : d11709 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1683, d11709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15834 q ha hb
    | true =>
      simp only [d1683, d11709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15817 q ha hb
  have h9 (q : Pattern) (ha : d4525 q = 1) (hb : d85721 q = 1) : d108980 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4525, d108980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4525, d108980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5649 q = 1) (hb : d85721 q = 1) : d11748 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5649, d11748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15836 q ha hb
    | true =>
      simp only [d5649, d11748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5650 q = 1) (hb : d85721 q = 1) : d11749 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5650, d11749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5650, d11749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74726 q = 1) (hb : d85721 q = 1) : d108981 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74726, d108981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74726, d108981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74727 q = 1) (hb : d85721 q = 1) : d108982 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74727, d108982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74727, d108982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74728 q = 1) (hb : d85721 q = 1) : d108983 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74728, d108983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74728, d108983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d1805 q = 1) (hb : d85721 q = 1) : d11756 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1805, d11756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15838 q ha hb
    | true =>
      simp only [d1805, d11756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15839 q ha hb
  have h16 (q : Pattern) (ha : d1806 q = 1) (hb : d85721 q = 1) : d11757 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1806, d11757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1806, d11757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1807 q = 1) (hb : d85721 q = 1) : d11758 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1807, d11758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d1807, d11758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d1808 q = 1) (hb : d85721 q = 1) : d11759 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d1808, d11759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1808, d11759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1811 q = 1) (hb : d85721 q = 1) : d11762 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1811, d11762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15840 q ha hb
    | true =>
      simp only [d1811, d11762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15841 q ha hb
  have h20 (q : Pattern) (ha : d1812 q = 1) (hb : d85721 q = 1) : d11763 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d1812, d11763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1812, d11763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d1813 q = 1) (hb : d85721 q = 1) : d11764 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d1813, d11764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d1813, d11764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d1815 q = 1) (hb : d85721 q = 1) : d11766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d11766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15842 q ha hb
    | true =>
      simp only [d1815, d11766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15820 q ha hb
  have h23 (q : Pattern) (ha : d4530 q = 1) (hb : d85721 q = 1) : d108985 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d108985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4530, d108985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5656 q = 1) (hb : d85721 q = 1) : d11772 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5656, d11772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15843 q ha hb
    | true =>
      simp only [d5656, d11772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5657 q = 1) (hb : d85721 q = 1) : d11773 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5657, d11773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5657, d11773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d74730 q = 1) (hb : d85721 q = 1) : d108986 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74730, d108986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d74730, d108986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d74731 q = 1) (hb : d85721 q = 1) : d108987 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74731, d108987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74731, d108987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d74732 q = 1) (hb : d85721 q = 1) : d108988 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74732, d108988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74732, d108988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d74733 q = 1) (hb : d85721 q = 1) : d108989 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74733, d108989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74733, d108989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro15845 (p : Pattern) (ha : d74740 p = 1) (hb : d85721 p = 1) : d108996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1815 q = 1) (hb : d85721 q = 1) : d11766 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1815, d11766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15842 q ha hb
    | true =>
      simp only [d1815, d11766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15820 q ha hb
  have h2 (q : Pattern) (ha : d4530 q = 1) (hb : d85721 q = 1) : d108985 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4530, d108985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4530, d108985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5656 q = 1) (hb : d85721 q = 1) : d11772 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5656, d11772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15843 q ha hb
    | true =>
      simp only [d5656, d11772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5657 q = 1) (hb : d85721 q = 1) : d11773 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5657, d11773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5657, d11773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74730 q = 1) (hb : d85721 q = 1) : d108986 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74730, d108986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74730, d108986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74738 q = 1) (hb : d85721 q = 1) : d108994 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74738, d108994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74738, d108994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74739 q = 1) (hb : d85721 q = 1) : d108995 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74739, d108995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74739, d108995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74740 q = 1) (hb : d85721 q = 1) : d108996 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74740, d108996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74740, d108996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15846 (p : Pattern) (ha : d1894 p = 1) (hb : d85721 p = 1) : d11817 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1867 q = 1) : d1867 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1873 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1874 q = 1) (hb : d85721 q = 1) : d11805 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1874, d85721, d11805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1874, d85721, d11805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1875 q = 1) (hb : d85721 q = 1) : d11806 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1875, d11806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1875, d11806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1876 q = 1) (hb : d85721 q = 1) : d11807 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1876, d11807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1876, d11807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1873 q = 1) : d1873 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1878 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1879 q = 1) (hb : d85721 q = 1) : d11808 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d85721, d11808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1879, d85721, d11808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1880 q = 1) (hb : d85721 q = 1) : d11809 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d11809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d11809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1881 q = 1) (hb : d85721 q = 1) : d11810 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d11810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d11810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1882 q = 1) (hb : d85721 q = 1) : d11811 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1882, d11811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1882, d11811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d1878 q = 1) : d1878 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d1888 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d1889 q = 1) (hb : d85721 q = 1) : d11812 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d85721, d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d1889, d85721, d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d1890 q = 1) (hb : d85721 q = 1) : d11813 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d11813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d11813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d1891 q = 1) (hb : d85721 q = 1) : d11814 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d11814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d11814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d1892 q = 1) (hb : d85721 q = 1) : d11815 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d11815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1892, d11815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d1893 q = 1) (hb : d85721 q = 1) : d11816 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1893, d11816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1893, d11816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d1894 q = 1) (hb : d85721 q = 1) : d11817 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1894, d11817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d1894, d11817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h19 p ha hb
theorem andIntro15847 (p : Pattern) (ha : d1899 p = 1) (hb : d85721 p = 1) : d11822 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1873 q = 1) : d1873 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1878 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1879 q = 1) (hb : d85721 q = 1) : d11808 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d85721, d11808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1879, d85721, d11808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1880 q = 1) (hb : d85721 q = 1) : d11809 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d11809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d11809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1881 q = 1) (hb : d85721 q = 1) : d11810 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d11810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d11810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1878 q = 1) : d1878 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1888 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1889 q = 1) (hb : d85721 q = 1) : d11812 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d85721, d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1889, d85721, d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1890 q = 1) (hb : d85721 q = 1) : d11813 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d11813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d11813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1891 q = 1) (hb : d85721 q = 1) : d11814 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d11814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d11814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1892 q = 1) (hb : d85721 q = 1) : d11815 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d11815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1892, d11815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1897 q = 1) (hb : d85721 q = 1) : d11820 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1897, d11820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d1897, d11820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d1898 q = 1) (hb : d85721 q = 1) : d11821 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d1898, d11821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d1898, d11821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d1899 q = 1) (hb : d85721 q = 1) : d11822 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d1899, d11822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d1899, d11822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro15848 (p : Pattern) (ha : d1905 p = 1) (hb : d85721 p = 1) : d11828 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1895 q = 1) (hb : d85721 q = 1) : d11818 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1895, d11818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15846 q ha hb
    | true =>
      simp only [d1895, d11818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1896 q = 1) (hb : d85721 q = 1) : d11819 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1896, d11819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1896, d11819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1900 q = 1) (hb : d85721 q = 1) : d11823 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1900, d11823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15847 q ha hb
    | true =>
      simp only [d1900, d11823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1901 q = 1) (hb : d85721 q = 1) : d11824 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1901, d11824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1901, d11824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1902 q = 1) (hb : d85721 q = 1) : d11825 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1902, d11825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1902, d11825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1903 q = 1) (hb : d85721 q = 1) : d11826 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1903, d11826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1903, d11826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1904 q = 1) (hb : d85721 q = 1) : d11827 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1904, d11827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1904, d11827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1905 q = 1) (hb : d85721 q = 1) : d11828 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1905, d11828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1905, d11828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15849 (p : Pattern) (ha : d1913 p = 1) (hb : d85721 p = 1) : d11836 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1900 q = 1) (hb : d85721 q = 1) : d11823 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1900, d11823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15847 q ha hb
    | true =>
      simp only [d1900, d11823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d1901 q = 1) (hb : d85721 q = 1) : d11824 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1901, d11824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1901, d11824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1908 q = 1) (hb : d85721 q = 1) : d11831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d1908, d11831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15826 q ha hb
    | true =>
      simp only [d1908, d11831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d1909 q = 1) (hb : d85721 q = 1) : d11832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d1909, d11832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1909, d11832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1910 q = 1) (hb : d85721 q = 1) : d11833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d1910, d11833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1910, d11833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1911 q = 1) (hb : d85721 q = 1) : d11834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d1911, d11834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1911, d11834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d1912 q = 1) (hb : d85721 q = 1) : d11835 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d1912, d11835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1912, d11835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d1913 q = 1) (hb : d85721 q = 1) : d11836 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d1913, d11836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1913, d11836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15850 (p : Pattern) (ha : d5686 p = 1) (hb : d85721 p = 1) : d11869 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d1873 q = 1) : d1873 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1878 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1879 q = 1) (hb : d85721 q = 1) : d11808 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1879, d85721, d11808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d1879, d85721, d11808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d1880 q = 1) (hb : d85721 q = 1) : d11809 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1880, d11809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1880, d11809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d1881 q = 1) (hb : d85721 q = 1) : d11810 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1881, d11810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1881, d11810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d1878 q = 1) : d1878 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d1888 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d1889 q = 1) (hb : d85721 q = 1) : d11812 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d1889, d85721, d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d1889, d85721, d11812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d1890 q = 1) (hb : d85721 q = 1) : d11813 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d1890, d11813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1890, d11813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d1891 q = 1) (hb : d85721 q = 1) : d11814 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d1891, d11814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1891, d11814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d1892 q = 1) (hb : d85721 q = 1) : d11815 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d1892, d11815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1892, d11815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d5679 q = 1) : d5679 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d5680 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d5681 q = 1) (hb : d85721 q = 1) : d11864 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5681, d85721, d11864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d5681, d85721, d11864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d5682 q = 1) (hb : d85721 q = 1) : d11865 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5682, d11865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5682, d11865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d5683 q = 1) (hb : d85721 q = 1) : d11866 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5683, d11866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5683, d11866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5684 q = 1) (hb : d85721 q = 1) : d11867 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5684, d11867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5684, d11867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5685 q = 1) (hb : d85721 q = 1) : d11868 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5685, d11868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5685, d11868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5686 q = 1) (hb : d85721 q = 1) : d11869 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5686, d11869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5686, d11869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h19 p ha hb
theorem andIntro15851 (p : Pattern) (ha : d5692 p = 1) (hb : d85721 p = 1) : d11875 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5687 q = 1) (hb : d85721 q = 1) : d11870 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5687, d11870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15850 q ha hb
    | true =>
      simp only [d5687, d11870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5688 q = 1) (hb : d85721 q = 1) : d11871 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5688, d11871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5688, d11871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5689 q = 1) (hb : d85721 q = 1) : d11872 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5689, d11872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5689, d11872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5690 q = 1) (hb : d85721 q = 1) : d11873 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5690, d11873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5690, d11873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5691 q = 1) (hb : d85721 q = 1) : d11874 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5691, d11874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5691, d11874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5692 q = 1) (hb : d85721 q = 1) : d11875 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5692, d11875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5692, d11875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15852 (p : Pattern) (ha : d74749 p = 1) (hb : d85721 p = 1) : d109006 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1914 q = 1) (hb : d85721 q = 1) : d11837 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d1914, d11837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15848 q ha hb
    | true =>
      simp only [d1914, d11837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15849 q ha hb
  have h2 (q : Pattern) (ha : d4545 q = 1) (hb : d85721 q = 1) : d109002 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4545, d109002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4545, d109002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5693 q = 1) (hb : d85721 q = 1) : d11876 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5693, d11876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15851 q ha hb
    | true =>
      simp only [d5693, d11876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5694 q = 1) (hb : d85721 q = 1) : d11877 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5694, d11877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5694, d11877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74746 q = 1) (hb : d85721 q = 1) : d109003 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74746, d109003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74746, d109003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74747 q = 1) (hb : d85721 q = 1) : d109004 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74747, d109004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74747, d109004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74748 q = 1) (hb : d85721 q = 1) : d109005 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74748, d109005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74748, d109005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74749 q = 1) (hb : d85721 q = 1) : d109006 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74749, d109006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74749, d109006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15853 (p : Pattern) (ha : d74755 p = 1) (hb : d85721 p = 1) : d109012 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1630 q = 1) (hb : d85721 q = 1) : d11667 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d11667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1630, d11667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15819 q ha hb
  have h2 (q : Pattern) (ha : d1631 q = 1) (hb : d85721 q = 1) : d11668 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d11668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1631, d11668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d1640 q = 1) (hb : d85721 q = 1) : d11677 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d11677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15819 q ha hb
    | true =>
      simp only [d1640, d11677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15822 q ha hb
  have h4 (q : Pattern) (ha : d1641 q = 1) (hb : d85721 q = 1) : d11678 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d11678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1641, d11678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d1642 q = 1) (hb : d85721 q = 1) : d11679 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d11679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1642, d11679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74734 q = 1) (hb : d85721 q = 1) : d108990 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74734, d108990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15837 q ha hb
    | true =>
      simp only [d74734, d108990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15844 q ha hb
  have h7 (q : Pattern) (ha : d1839 q = 1) (hb : d85721 q = 1) : d11791 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, d11791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15823 q ha hb
    | true =>
      simp only [d1839, d11791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15824 q ha hb
  have h8 (q : Pattern) (ha : d74735 q = 1) (hb : d85721 q = 1) : d108991 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74735, d108991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74735, d108991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74736 q = 1) (hb : d85721 q = 1) : d108992 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74736, d108992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74736, d108992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d74737 q = 1) (hb : d85721 q = 1) : d108993 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74737, d108993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74737, d108993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74741 q = 1) (hb : d85721 q = 1) : d108997 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74741, d108997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74741, d108997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15845 q ha hb
  have h12 (q : Pattern) (ha : d1848 q = 1) (hb : d85721 q = 1) : d11800 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d11800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1848, d11800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15825 q ha hb
  have h13 (q : Pattern) (ha : d74742 q = 1) (hb : d85721 q = 1) : d108998 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74742, d108998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74742, d108998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74743 q = 1) (hb : d85721 q = 1) : d108999 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74743, d108999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74743, d108999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d74744 q = 1) (hb : d85721 q = 1) : d109000 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74744, d109000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74744, d109000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d74745 q = 1) (hb : d85721 q = 1) : d109001 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74745, d109001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74745, d109001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74750 q = 1) (hb : d85721 q = 1) : d109007 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74750, d109007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74750, d109007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15852 q ha hb
  have h18 (q : Pattern) (ha : d1981 q = 1) (hb : d85721 q = 1) : d11893 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1981, d11893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1981, d11893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15828 q ha hb
  have h19 (q : Pattern) (ha : d74751 q = 1) (hb : d85721 q = 1) : d109008 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74751, d109008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74751, d109008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d74752 q = 1) (hb : d85721 q = 1) : d109009 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74752, d109009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74752, d109009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d74753 q = 1) (hb : d85721 q = 1) : d109010 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74753, d109010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74753, d109010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d74754 q = 1) (hb : d85721 q = 1) : d109011 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74754, d109011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74754, d109011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d74755 q = 1) (hb : d85721 q = 1) : d109012 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74755, d109012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74755, d109012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro15854 (p : Pattern) (ha : d74761 p = 1) (hb : d85721 p = 1) : d109018 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74756 q = 1) (hb : d85721 q = 1) : d109013 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74756, d109013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74756, d109013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15853 q ha hb
  have h2 (q : Pattern) (ha : d74757 q = 1) (hb : d85721 q = 1) : d109014 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74757, d109014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74757, d109014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74758 q = 1) (hb : d85721 q = 1) : d109015 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74758, d109015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74758, d109015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74759 q = 1) (hb : d85721 q = 1) : d109016 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74759, d109016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74759, d109016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74760 q = 1) (hb : d85721 q = 1) : d109017 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74760, d109017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74760, d109017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74761 q = 1) (hb : d85721 q = 1) : d109018 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74761, d109018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74761, d109018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15855 (p : Pattern) (ha : d2092 p = 1) (hb : d85721 p = 1) : d11918 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2070 q = 1) : d2070 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2072 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2073 q = 1) (hb : d85721 q = 1) : d11909 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d85721, d11909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2073, d85721, d11909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2074 q = 1) (hb : d85721 q = 1) : d11910 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d11910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d11910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2075 q = 1) (hb : d85721 q = 1) : d11911 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d11911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d11911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d2072 q = 1) : d2072 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2085 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2086 q = 1) (hb : d85721 q = 1) : d11912 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d85721, d11912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2086, d85721, d11912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2087 q = 1) (hb : d85721 q = 1) : d11913 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d11913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2087, d11913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2088 q = 1) (hb : d85721 q = 1) : d11914 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d11914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2088, d11914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2089 q = 1) (hb : d85721 q = 1) : d11915 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2089, d11915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2089, d11915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2090 q = 1) (hb : d85721 q = 1) : d11916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2090, d11916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2090, d11916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2091 q = 1) (hb : d85721 q = 1) : d11917 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2091, d11917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2091, d11917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2092 q = 1) (hb : d85721 q = 1) : d11918 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2092, d11918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2092, d11918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro15856 (p : Pattern) (ha : d2096 p = 1) (hb : d85721 p = 1) : d11922 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2072 q = 1) : d2072 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2085 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2086 q = 1) (hb : d85721 q = 1) : d11912 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d85721, d11912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2086, d85721, d11912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2087 q = 1) (hb : d85721 q = 1) : d11913 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d11913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2087, d11913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2088 q = 1) (hb : d85721 q = 1) : d11914 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d11914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2088, d11914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2090 q = 1) (hb : d85721 q = 1) : d11916 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2090, d11916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2090, d11916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2095 q = 1) (hb : d85721 q = 1) : d11921 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2095, d11921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2095, d11921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2096 q = 1) (hb : d85721 q = 1) : d11922 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2096, d11922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2096, d11922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15857 (p : Pattern) (ha : d2102 p = 1) (hb : d85721 p = 1) : d11928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d85721 q = 1) : d11919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d11919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15855 q ha hb
    | true =>
      simp only [d2093, d11919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d85721 q = 1) : d11920 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d11920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d11920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d85721 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15856 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d85721 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d85721 q = 1) : d11925 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d11925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d11925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2100 q = 1) (hb : d85721 q = 1) : d11926 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d11926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2100, d11926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2101 q = 1) (hb : d85721 q = 1) : d11927 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2101, d11927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2101, d11927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2102 q = 1) (hb : d85721 q = 1) : d11928 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2102, d11928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2102, d11928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15858 (p : Pattern) (ha : d2106 p = 1) (hb : d85721 p = 1) : d11932 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d85721 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15856 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d85721 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d85721 q = 1) : d11929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d85721 q = 1) : d11930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2105 q = 1) (hb : d85721 q = 1) : d11931 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, d11931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2105, d11931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2106 q = 1) (hb : d85721 q = 1) : d11932 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2106, d11932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2106, d11932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15859 (p : Pattern) (ha : d2112 p = 1) (hb : d85721 p = 1) : d11938 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2107 q = 1) (hb : d85721 q = 1) : d11933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d11933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15857 q ha hb
    | true =>
      simp only [d2107, d11933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15858 q ha hb
  have h2 (q : Pattern) (ha : d2108 q = 1) (hb : d85721 q = 1) : d11934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d11934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, d11934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2109 q = 1) (hb : d85721 q = 1) : d11935 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d11935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2109, d11935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2110 q = 1) (hb : d85721 q = 1) : d11936 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d11936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d11936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2111 q = 1) (hb : d85721 q = 1) : d11937 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d11937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d11937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2112 q = 1) (hb : d85721 q = 1) : d11938 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2112, d11938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2112, d11938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15860 (p : Pattern) (ha : d2115 p = 1) (hb : d85721 p = 1) : d11941 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d85721 q = 1) : d11919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d11919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15855 q ha hb
    | true =>
      simp only [d2093, d11919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d85721 q = 1) : d11920 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d11920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d11920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d85721 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15856 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d85721 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d85721 q = 1) : d11925 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d11925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d11925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2100 q = 1) (hb : d85721 q = 1) : d11926 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d11926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2100, d11926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2101 q = 1) (hb : d85721 q = 1) : d11927 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2101, d11927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2101, d11927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2115 q = 1) (hb : d85721 q = 1) : d11941 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2115, d11941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2115, d11941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15861 (p : Pattern) (ha : d2116 p = 1) (hb : d85721 p = 1) : d11942 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d85721 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15856 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d85721 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d85721 q = 1) : d11929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d85721 q = 1) : d11930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2105 q = 1) (hb : d85721 q = 1) : d11931 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2105, d11931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2105, d11931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2116 q = 1) (hb : d85721 q = 1) : d11942 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2116, d11942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2116, d11942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15862 (p : Pattern) (ha : d2122 p = 1) (hb : d85721 p = 1) : d11948 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2107 q = 1) (hb : d85721 q = 1) : d11933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d11933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15857 q ha hb
    | true =>
      simp only [d2107, d11933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15858 q ha hb
  have h2 (q : Pattern) (ha : d2108 q = 1) (hb : d85721 q = 1) : d11934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d11934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, d11934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2109 q = 1) (hb : d85721 q = 1) : d11935 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d11935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2109, d11935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2110 q = 1) (hb : d85721 q = 1) : d11936 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d11936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d11936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2111 q = 1) (hb : d85721 q = 1) : d11937 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d11937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d11937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2117 q = 1) (hb : d85721 q = 1) : d11943 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2117, d11943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15860 q ha hb
    | true =>
      simp only [d2117, d11943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15861 q ha hb
  have h7 (q : Pattern) (ha : d2118 q = 1) (hb : d85721 q = 1) : d11944 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2118, d11944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2118, d11944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2119 q = 1) (hb : d85721 q = 1) : d11945 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2119, d11945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2119, d11945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2120 q = 1) (hb : d85721 q = 1) : d11946 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2120, d11946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2120, d11946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2121 q = 1) (hb : d85721 q = 1) : d11947 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2121, d11947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2121, d11947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2122 q = 1) (hb : d85721 q = 1) : d11948 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2122, d11948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2122, d11948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15863 (p : Pattern) (ha : d2310 p = 1) (hb : d85721 p = 1) : d12056 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2107 q = 1) (hb : d85721 q = 1) : d11933 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2107, d11933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15857 q ha hb
    | true =>
      simp only [d2107, d11933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15858 q ha hb
  have h2 (q : Pattern) (ha : d2108 q = 1) (hb : d85721 q = 1) : d11934 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2108, d11934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2108, d11934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2109 q = 1) (hb : d85721 q = 1) : d11935 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2109, d11935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2109, d11935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2110 q = 1) (hb : d85721 q = 1) : d11936 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2110, d11936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2110, d11936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2111 q = 1) (hb : d85721 q = 1) : d11937 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2111, d11937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2111, d11937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2305 q = 1) (hb : d85721 q = 1) : d12051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d12051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15858 q ha hb
    | true =>
      simp only [d2305, d12051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2306 q = 1) (hb : d85721 q = 1) : d12052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d12052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d12052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2307 q = 1) (hb : d85721 q = 1) : d12053 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d12053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2307, d12053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2308 q = 1) (hb : d85721 q = 1) : d12054 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d12054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d12054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2309 q = 1) (hb : d85721 q = 1) : d12055 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d12055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d12055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2310 q = 1) (hb : d85721 q = 1) : d12056 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2310, d12056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2310, d12056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15864 (p : Pattern) (ha : d2316 p = 1) (hb : d85721 p = 1) : d12062 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2305 q = 1) (hb : d85721 q = 1) : d12051 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2305, d12051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15858 q ha hb
    | true =>
      simp only [d2305, d12051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2306 q = 1) (hb : d85721 q = 1) : d12052 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2306, d12052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2306, d12052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2307 q = 1) (hb : d85721 q = 1) : d12053 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2307, d12053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2307, d12053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2308 q = 1) (hb : d85721 q = 1) : d12054 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2308, d12054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2308, d12054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2309 q = 1) (hb : d85721 q = 1) : d12055 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2309, d12055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2309, d12055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2311 q = 1) (hb : d85721 q = 1) : d12057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, d12057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15861 q ha hb
    | true =>
      simp only [d2311, d12057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2312 q = 1) (hb : d85721 q = 1) : d12058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d12058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2312, d12058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2313 q = 1) (hb : d85721 q = 1) : d12059 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d12059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2313, d12059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d2314 q = 1) (hb : d85721 q = 1) : d12060 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, d12060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, d12060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2315 q = 1) (hb : d85721 q = 1) : d12061 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, d12061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, d12061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2316 q = 1) (hb : d85721 q = 1) : d12062 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2316, d12062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2316, d12062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15865 (p : Pattern) (ha : d2325 p = 1) (hb : d85721 p = 1) : d12071 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2311 q = 1) (hb : d85721 q = 1) : d12057 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2311, d12057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15861 q ha hb
    | true =>
      simp only [d2311, d12057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2312 q = 1) (hb : d85721 q = 1) : d12058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2312, d12058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2312, d12058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2313 q = 1) (hb : d85721 q = 1) : d12059 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2313, d12059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2313, d12059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2314 q = 1) (hb : d85721 q = 1) : d12060 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2314, d12060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2314, d12060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2315 q = 1) (hb : d85721 q = 1) : d12061 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2315, d12061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2315, d12061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2325 q = 1) (hb : d85721 q = 1) : d12071 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2325, d12071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2325, d12071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15866 (p : Pattern) (ha : d2385 p = 1) (hb : d85721 p = 1) : d12102 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2356 q = 1) : d2356 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2366 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2367 q = 1) (hb : d85721 q = 1) : d12084 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d85721, d12084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2367, d85721, d12084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2368 q = 1) (hb : d85721 q = 1) : d12085 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d12085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d12085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2369 q = 1) (hb : d85721 q = 1) : d12086 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d12086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d12086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2375 q = 1) (hb : d85721 q = 1) : d12092 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2375, d12092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2375, d12092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2384 q = 1) (hb : d85721 q = 1) : d12101 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2384, d12101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2384, d12101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2385 q = 1) (hb : d85721 q = 1) : d12102 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2385, d12102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2385, d12102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15867 (p : Pattern) (ha : d2452 p = 1) (hb : d85721 p = 1) : d12158 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2386 q = 1) (hb : d85721 q = 1) : d12103 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d12103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15866 q ha hb
    | true =>
      simp only [d2386, d12103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2387 q = 1) (hb : d85721 q = 1) : d12104 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d12104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d12104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2449 q = 1) (hb : d85721 q = 1) : d12155 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2449, d12155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2449, d12155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2450 q = 1) (hb : d85721 q = 1) : d12156 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2450, d12156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2450, d12156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2451 q = 1) (hb : d85721 q = 1) : d12157 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2451, d12157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2451, d12157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2452 q = 1) (hb : d85721 q = 1) : d12158 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2452, d12158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2452, d12158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15868 (p : Pattern) (ha : d2458 p = 1) (hb : d85721 p = 1) : d12164 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2453 q = 1) (hb : d85721 q = 1) : d12159 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2453, d12159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15867 q ha hb
    | true =>
      simp only [d2453, d12159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2454 q = 1) (hb : d85721 q = 1) : d12160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2454, d12160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2454, d12160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2455 q = 1) (hb : d85721 q = 1) : d12161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2455, d12161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2455, d12161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2456 q = 1) (hb : d85721 q = 1) : d12162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2456, d12162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2456, d12162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2457 q = 1) (hb : d85721 q = 1) : d12163 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d2457, d12163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2457, d12163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2458 q = 1) (hb : d85721 q = 1) : d12164 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d2458, d12164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2458, d12164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15869 (p : Pattern) (ha : d2127 p = 1) (hb : d85721 p = 1) : d11953 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d85721 q = 1) : d11919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d11919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15855 q ha hb
    | true =>
      simp only [d2093, d11919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d85721 q = 1) : d11920 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d11920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d11920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d85721 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15856 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d85721 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d85721 q = 1) : d11925 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d11925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d11925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2100 q = 1) (hb : d85721 q = 1) : d11926 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d11926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2100, d11926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2126 q = 1) (hb : d85721 q = 1) : d11952 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2126, d11952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2126, d11952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2127 q = 1) (hb : d85721 q = 1) : d11953 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2127, d11953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2127, d11953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15870 (p : Pattern) (ha : d2129 p = 1) (hb : d85721 p = 1) : d11955 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d85721 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15856 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d85721 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d85721 q = 1) : d11929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d85721 q = 1) : d11930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2128 q = 1) (hb : d85721 q = 1) : d11954 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, d11954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, d11954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2129 q = 1) (hb : d85721 q = 1) : d11955 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2129, d11955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2129, d11955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15871 (p : Pattern) (ha : d2136 p = 1) (hb : d85721 p = 1) : d11962 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d85721 q = 1) : d11919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d11919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15855 q ha hb
    | true =>
      simp only [d2093, d11919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d85721 q = 1) : d11920 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d11920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d11920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d85721 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15856 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d85721 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d85721 q = 1) : d11925 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d11925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d11925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2134 q = 1) (hb : d85721 q = 1) : d11960 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2134, d11960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2134, d11960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2135 q = 1) (hb : d85721 q = 1) : d11961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2135, d11961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2135, d11961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2136 q = 1) (hb : d85721 q = 1) : d11962 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2136, d11962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2136, d11962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15872 (p : Pattern) (ha : d2139 p = 1) (hb : d85721 p = 1) : d11965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d85721 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15856 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d85721 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d85721 q = 1) : d11929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2137 q = 1) (hb : d85721 q = 1) : d11963 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, d11963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, d11963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2138 q = 1) (hb : d85721 q = 1) : d11964 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, d11964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2138, d11964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2139 q = 1) (hb : d85721 q = 1) : d11965 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2139, d11965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2139, d11965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15873 (p : Pattern) (ha : d2155 p = 1) (hb : d85721 p = 1) : d11974 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2149 q = 1) : d2149 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2070 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2150 q = 1) (hb : d85721 q = 1) : d11969 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2150, d85721, d11969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2150, d85721, d11969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2151 q = 1) (hb : d85721 q = 1) : d11970 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2151, d11970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2151, d11970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2152 q = 1) (hb : d85721 q = 1) : d11971 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2152, d11971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2152, d11971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d2070 q = 1) : d2070 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2072 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2073 q = 1) (hb : d85721 q = 1) : d11909 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d85721, d11909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2073, d85721, d11909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2074 q = 1) (hb : d85721 q = 1) : d11910 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d11910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d11910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2075 q = 1) (hb : d85721 q = 1) : d11911 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d11911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d11911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2153 q = 1) (hb : d85721 q = 1) : d11972 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2153, d11972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2153, d11972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d2072 q = 1) : d2072 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d2085 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2086 q = 1) (hb : d85721 q = 1) : d11912 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d85721, d11912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d2086, d85721, d11912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d2087 q = 1) (hb : d85721 q = 1) : d11913 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d11913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2087, d11913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2088 q = 1) (hb : d85721 q = 1) : d11914 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d11914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2088, d11914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d2089 q = 1) (hb : d85721 q = 1) : d11915 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2089, d11915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2089, d11915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d2154 q = 1) (hb : d85721 q = 1) : d11973 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2154, d11973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2154, d11973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d2155 q = 1) (hb : d85721 q = 1) : d11974 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2155, d11974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d2155, d11974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h19 p ha hb
theorem andIntro15874 (p : Pattern) (ha : d2161 p = 1) (hb : d85721 p = 1) : d11980 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2156 q = 1) (hb : d85721 q = 1) : d11975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2156, d11975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15873 q ha hb
    | true =>
      simp only [d2156, d11975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2157 q = 1) (hb : d85721 q = 1) : d11976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, d11976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2157, d11976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2093 q = 1) (hb : d85721 q = 1) : d11919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d11919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15855 q ha hb
    | true =>
      simp only [d2093, d11919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2094 q = 1) (hb : d85721 q = 1) : d11920 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d11920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d11920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2158 q = 1) (hb : d85721 q = 1) : d11977 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2158, d11977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2158, d11977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2159 q = 1) (hb : d85721 q = 1) : d11978 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2159, d11978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2159, d11978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2160 q = 1) (hb : d85721 q = 1) : d11979 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2160, d11979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2160, d11979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2161 q = 1) (hb : d85721 q = 1) : d11980 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2161, d11980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2161, d11980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15875 (p : Pattern) (ha : d5733 p = 1) (hb : d85721 p = 1) : d12013 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2070 q = 1) : d2070 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2072 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2073 q = 1) (hb : d85721 q = 1) : d11909 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2073, d85721, d11909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2073, d85721, d11909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2074 q = 1) (hb : d85721 q = 1) : d11910 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2074, d11910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2074, d11910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2075 q = 1) (hb : d85721 q = 1) : d11911 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2075, d11911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2075, d11911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d2072 q = 1) : d2072 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2085 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2086 q = 1) (hb : d85721 q = 1) : d11912 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2086, d85721, d11912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2086, d85721, d11912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2087 q = 1) (hb : d85721 q = 1) : d11913 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2087, d11913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2087, d11913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2088 q = 1) (hb : d85721 q = 1) : d11914 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2088, d11914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2088, d11914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2089 q = 1) (hb : d85721 q = 1) : d11915 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2089, d11915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2089, d11915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d5726 q = 1) : d5726 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d5727 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d5728 q = 1) (hb : d85721 q = 1) : d12008 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5728, d85721, d12008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d5728, d85721, d12008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d5729 q = 1) (hb : d85721 q = 1) : d12009 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5729, d12009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5729, d12009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d5730 q = 1) (hb : d85721 q = 1) : d12010 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5730, d12010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5730, d12010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5731 q = 1) (hb : d85721 q = 1) : d12011 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5731, d12011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5731, d12011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5732 q = 1) (hb : d85721 q = 1) : d12012 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5732, d12012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5732, d12012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5733 q = 1) (hb : d85721 q = 1) : d12013 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5733, d12013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5733, d12013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h19 p ha hb
theorem andIntro15876 (p : Pattern) (ha : d5739 p = 1) (hb : d85721 p = 1) : d12019 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5734 q = 1) (hb : d85721 q = 1) : d12014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5734, d12014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15875 q ha hb
    | true =>
      simp only [d5734, d12014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5735 q = 1) (hb : d85721 q = 1) : d12015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5735, d12015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5735, d12015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5736 q = 1) (hb : d85721 q = 1) : d12016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5736, d12016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5736, d12016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5737 q = 1) (hb : d85721 q = 1) : d12017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5737, d12017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5737, d12017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5738 q = 1) (hb : d85721 q = 1) : d12018 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5738, d12018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5738, d12018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5739 q = 1) (hb : d85721 q = 1) : d12019 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5739, d12019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5739, d12019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15877 (p : Pattern) (ha : d74769 p = 1) (hb : d85721 p = 1) : d109027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2130 q = 1) (hb : d85721 q = 1) : d11956 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d11956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15869 q ha hb
    | true =>
      simp only [d2130, d11956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15870 q ha hb
  have h2 (q : Pattern) (ha : d2131 q = 1) (hb : d85721 q = 1) : d11957 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d11957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, d11957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2132 q = 1) (hb : d85721 q = 1) : d11958 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d11958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2132, d11958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2133 q = 1) (hb : d85721 q = 1) : d11959 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d11959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d11959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2140 q = 1) (hb : d85721 q = 1) : d11966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d11966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15871 q ha hb
    | true =>
      simp only [d2140, d11966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15872 q ha hb
  have h6 (q : Pattern) (ha : d2141 q = 1) (hb : d85721 q = 1) : d11967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d11967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d11967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2142 q = 1) (hb : d85721 q = 1) : d11968 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d11968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2142, d11968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2162 q = 1) (hb : d85721 q = 1) : d11981 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d11981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15874 q ha hb
    | true =>
      simp only [d2162, d11981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15857 q ha hb
  have h9 (q : Pattern) (ha : d4566 q = 1) (hb : d85721 q = 1) : d109023 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d109023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4566, d109023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5740 q = 1) (hb : d85721 q = 1) : d12020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5740, d12020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15876 q ha hb
    | true =>
      simp only [d5740, d12020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5741 q = 1) (hb : d85721 q = 1) : d12021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5741, d12021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5741, d12021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74766 q = 1) (hb : d85721 q = 1) : d109024 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74766, d109024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74766, d109024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74767 q = 1) (hb : d85721 q = 1) : d109025 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74767, d109025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74767, d109025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74768 q = 1) (hb : d85721 q = 1) : d109026 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74768, d109026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74768, d109026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74769 q = 1) (hb : d85721 q = 1) : d109027 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74769, d109027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74769, d109027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro15878 (p : Pattern) (ha : d2281 p = 1) (hb : d85721 p = 1) : d12026 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d85721 q = 1) : d11919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d11919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15855 q ha hb
    | true =>
      simp only [d2093, d11919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d85721 q = 1) : d11920 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d11920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d11920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d85721 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15856 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d85721 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d85721 q = 1) : d11925 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d11925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d11925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2100 q = 1) (hb : d85721 q = 1) : d11926 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2100, d11926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2100, d11926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2126 q = 1) (hb : d85721 q = 1) : d11952 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2126, d11952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2126, d11952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2281 q = 1) (hb : d85721 q = 1) : d12026 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2281, d12026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2281, d12026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15879 (p : Pattern) (ha : d2282 p = 1) (hb : d85721 p = 1) : d12027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d85721 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15856 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d85721 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d85721 q = 1) : d11929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2104 q = 1) (hb : d85721 q = 1) : d11930 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2104, d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2104, d11930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2128 q = 1) (hb : d85721 q = 1) : d11954 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2128, d11954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2128, d11954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2282 q = 1) (hb : d85721 q = 1) : d12027 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2282, d12027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2282, d12027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15880 (p : Pattern) (ha : d2287 p = 1) (hb : d85721 p = 1) : d12032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2093 q = 1) (hb : d85721 q = 1) : d11919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d11919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15855 q ha hb
    | true =>
      simp only [d2093, d11919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2094 q = 1) (hb : d85721 q = 1) : d11920 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d11920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d11920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2097 q = 1) (hb : d85721 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15856 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2098 q = 1) (hb : d85721 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2099 q = 1) (hb : d85721 q = 1) : d11925 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2099, d11925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2099, d11925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2134 q = 1) (hb : d85721 q = 1) : d11960 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2134, d11960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2134, d11960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2135 q = 1) (hb : d85721 q = 1) : d11961 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2135, d11961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2135, d11961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2287 q = 1) (hb : d85721 q = 1) : d12032 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2287, d12032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2287, d12032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15881 (p : Pattern) (ha : d2288 p = 1) (hb : d85721 p = 1) : d12033 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2097 q = 1) (hb : d85721 q = 1) : d11923 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15856 q ha hb
    | true =>
      simp only [d2097, d11923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2098 q = 1) (hb : d85721 q = 1) : d11924 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2098, d11924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2103 q = 1) (hb : d85721 q = 1) : d11929 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2103, d11929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2137 q = 1) (hb : d85721 q = 1) : d11963 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2137, d11963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2137, d11963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2138 q = 1) (hb : d85721 q = 1) : d11964 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2138, d11964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d2138, d11964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d2288 q = 1) (hb : d85721 q = 1) : d12033 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2288, d12033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2288, d12033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15882 (p : Pattern) (ha : d2292 p = 1) (hb : d85721 p = 1) : d12037 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2156 q = 1) (hb : d85721 q = 1) : d11975 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2156, d11975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15873 q ha hb
    | true =>
      simp only [d2156, d11975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2157 q = 1) (hb : d85721 q = 1) : d11976 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2157, d11976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2157, d11976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2093 q = 1) (hb : d85721 q = 1) : d11919 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2093, d11919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15855 q ha hb
    | true =>
      simp only [d2093, d11919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2094 q = 1) (hb : d85721 q = 1) : d11920 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2094, d11920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2094, d11920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2158 q = 1) (hb : d85721 q = 1) : d11977 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2158, d11977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2158, d11977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2159 q = 1) (hb : d85721 q = 1) : d11978 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2159, d11978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2159, d11978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2160 q = 1) (hb : d85721 q = 1) : d11979 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2160, d11979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2160, d11979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2292 q = 1) (hb : d85721 q = 1) : d12037 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2292, d12037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2292, d12037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15883 (p : Pattern) (ha : d5746 p = 1) (hb : d85721 p = 1) : d12043 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5734 q = 1) (hb : d85721 q = 1) : d12014 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5734, d12014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15875 q ha hb
    | true =>
      simp only [d5734, d12014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5735 q = 1) (hb : d85721 q = 1) : d12015 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5735, d12015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5735, d12015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5736 q = 1) (hb : d85721 q = 1) : d12016 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5736, d12016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5736, d12016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5737 q = 1) (hb : d85721 q = 1) : d12017 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5737, d12017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5737, d12017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5738 q = 1) (hb : d85721 q = 1) : d12018 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5738, d12018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5738, d12018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5746 q = 1) (hb : d85721 q = 1) : d12043 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5746, d12043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5746, d12043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15884 (p : Pattern) (ha : d74773 p = 1) (hb : d85721 p = 1) : d109032 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2130 q = 1) (hb : d85721 q = 1) : d11956 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2130, d11956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15869 q ha hb
    | true =>
      simp only [d2130, d11956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15870 q ha hb
  have h2 (q : Pattern) (ha : d2131 q = 1) (hb : d85721 q = 1) : d11957 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2131, d11957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2131, d11957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2132 q = 1) (hb : d85721 q = 1) : d11958 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2132, d11958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2132, d11958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2133 q = 1) (hb : d85721 q = 1) : d11959 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2133, d11959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2133, d11959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2140 q = 1) (hb : d85721 q = 1) : d11966 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2140, d11966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15871 q ha hb
    | true =>
      simp only [d2140, d11966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15872 q ha hb
  have h6 (q : Pattern) (ha : d2141 q = 1) (hb : d85721 q = 1) : d11967 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2141, d11967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2141, d11967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2142 q = 1) (hb : d85721 q = 1) : d11968 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2142, d11968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2142, d11968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2162 q = 1) (hb : d85721 q = 1) : d11981 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2162, d11981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15874 q ha hb
    | true =>
      simp only [d2162, d11981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15857 q ha hb
  have h9 (q : Pattern) (ha : d4566 q = 1) (hb : d85721 q = 1) : d109023 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4566, d109023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d4566, d109023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d5740 q = 1) (hb : d85721 q = 1) : d12020 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5740, d12020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15876 q ha hb
    | true =>
      simp only [d5740, d12020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d5741 q = 1) (hb : d85721 q = 1) : d12021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5741, d12021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d5741, d12021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d74766 q = 1) (hb : d85721 q = 1) : d109024 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74766, d109024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d74766, d109024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74767 q = 1) (hb : d85721 q = 1) : d109025 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74767, d109025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d74767, d109025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74768 q = 1) (hb : d85721 q = 1) : d109026 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74768, d109026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74768, d109026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d2283 q = 1) (hb : d85721 q = 1) : d12028 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2283, d12028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15878 q ha hb
    | true =>
      simp only [d2283, d12028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15879 q ha hb
  have h16 (q : Pattern) (ha : d2284 q = 1) (hb : d85721 q = 1) : d12029 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2284, d12029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2284, d12029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d2285 q = 1) (hb : d85721 q = 1) : d12030 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2285, d12030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d2285, d12030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d2286 q = 1) (hb : d85721 q = 1) : d12031 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d2286, d12031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2286, d12031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d2289 q = 1) (hb : d85721 q = 1) : d12034 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2289, d12034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15880 q ha hb
    | true =>
      simp only [d2289, d12034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15881 q ha hb
  have h20 (q : Pattern) (ha : d2290 q = 1) (hb : d85721 q = 1) : d12035 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d2290, d12035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2290, d12035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
  have h21 (q : Pattern) (ha : d2291 q = 1) (hb : d85721 q = 1) : d12036 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d2291, d12036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d2291, d12036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d2293 q = 1) (hb : d85721 q = 1) : d12038 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d12038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15882 q ha hb
    | true =>
      simp only [d2293, d12038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15860 q ha hb
  have h23 (q : Pattern) (ha : d4571 q = 1) (hb : d85721 q = 1) : d109028 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d109028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d4571, d109028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h24 (q : Pattern) (ha : d5747 q = 1) (hb : d85721 q = 1) : d12044 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5747, d12044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15883 q ha hb
    | true =>
      simp only [d5747, d12044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h25 (q : Pattern) (ha : d5748 q = 1) (hb : d85721 q = 1) : d12045 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5748, d12045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q ha hb
    | true =>
      simp only [d5748, d12045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h26 (q : Pattern) (ha : d74770 q = 1) (hb : d85721 q = 1) : d109029 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74770, d109029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d74770, d109029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
  have h27 (q : Pattern) (ha : d74771 q = 1) (hb : d85721 q = 1) : d109030 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74771, d109030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74771, d109030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
  have h28 (q : Pattern) (ha : d74772 q = 1) (hb : d85721 q = 1) : d109031 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74772, d109031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d74772, d109031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d74773 q = 1) (hb : d85721 q = 1) : d109032 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74773, d109032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74773, d109032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  exact h29 p ha hb
theorem andIntro15885 (p : Pattern) (ha : d74780 p = 1) (hb : d85721 p = 1) : d109039 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2293 q = 1) (hb : d85721 q = 1) : d12038 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2293, d12038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15882 q ha hb
    | true =>
      simp only [d2293, d12038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15860 q ha hb
  have h2 (q : Pattern) (ha : d4571 q = 1) (hb : d85721 q = 1) : d109028 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4571, d109028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4571, d109028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5747 q = 1) (hb : d85721 q = 1) : d12044 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5747, d12044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15883 q ha hb
    | true =>
      simp only [d5747, d12044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5748 q = 1) (hb : d85721 q = 1) : d12045 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5748, d12045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5748, d12045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74770 q = 1) (hb : d85721 q = 1) : d109029 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74770, d109029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74770, d109029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74778 q = 1) (hb : d85721 q = 1) : d109037 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74778, d109037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74778, d109037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74779 q = 1) (hb : d85721 q = 1) : d109038 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74779, d109038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74779, d109038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74780 q = 1) (hb : d85721 q = 1) : d109039 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74780, d109039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74780, d109039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15886 (p : Pattern) (ha : d2372 p = 1) (hb : d85721 p = 1) : d12089 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2345 q = 1) : d2345 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2351 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2352 q = 1) (hb : d85721 q = 1) : d12077 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2352, d85721, d12077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2352, d85721, d12077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2353 q = 1) (hb : d85721 q = 1) : d12078 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2353, d12078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2353, d12078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2354 q = 1) (hb : d85721 q = 1) : d12079 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2354, d12079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2354, d12079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d2351 q = 1) : d2351 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2356 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2357 q = 1) (hb : d85721 q = 1) : d12080 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d85721, d12080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2357, d85721, d12080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2358 q = 1) (hb : d85721 q = 1) : d12081 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d12081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d12081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2359 q = 1) (hb : d85721 q = 1) : d12082 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d12082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d12082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2360 q = 1) (hb : d85721 q = 1) : d12083 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2360, d12083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2360, d12083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d2356 q = 1) : d2356 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d2366 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d2367 q = 1) (hb : d85721 q = 1) : d12084 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d85721, d12084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d2367, d85721, d12084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d2368 q = 1) (hb : d85721 q = 1) : d12085 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d12085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d12085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d2369 q = 1) (hb : d85721 q = 1) : d12086 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d12086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d12086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d2370 q = 1) (hb : d85721 q = 1) : d12087 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d12087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2370, d12087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d2371 q = 1) (hb : d85721 q = 1) : d12088 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2371, d12088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2371, d12088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d2372 q = 1) (hb : d85721 q = 1) : d12089 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2372, d12089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d2372, d12089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h19 p ha hb
theorem andIntro15887 (p : Pattern) (ha : d2377 p = 1) (hb : d85721 p = 1) : d12094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2351 q = 1) : d2351 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2356 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2357 q = 1) (hb : d85721 q = 1) : d12080 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d85721, d12080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2357, d85721, d12080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2358 q = 1) (hb : d85721 q = 1) : d12081 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d12081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d12081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2359 q = 1) (hb : d85721 q = 1) : d12082 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d12082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d12082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d2356 q = 1) : d2356 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2366 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2367 q = 1) (hb : d85721 q = 1) : d12084 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d85721, d12084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2367, d85721, d12084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2368 q = 1) (hb : d85721 q = 1) : d12085 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d12085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d12085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2369 q = 1) (hb : d85721 q = 1) : d12086 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d12086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d12086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2370 q = 1) (hb : d85721 q = 1) : d12087 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d12087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2370, d12087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d2375 q = 1) (hb : d85721 q = 1) : d12092 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2375, d12092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d2375, d12092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d2376 q = 1) (hb : d85721 q = 1) : d12093 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d2376, d12093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d2376, d12093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d2377 q = 1) (hb : d85721 q = 1) : d12094 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d2377, d12094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d2377, d12094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h14 p ha hb
theorem andIntro15888 (p : Pattern) (ha : d2383 p = 1) (hb : d85721 p = 1) : d12100 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2373 q = 1) (hb : d85721 q = 1) : d12090 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2373, d12090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15886 q ha hb
    | true =>
      simp only [d2373, d12090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2374 q = 1) (hb : d85721 q = 1) : d12091 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2374, d12091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2374, d12091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2378 q = 1) (hb : d85721 q = 1) : d12095 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2378, d12095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15887 q ha hb
    | true =>
      simp only [d2378, d12095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2379 q = 1) (hb : d85721 q = 1) : d12096 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2379, d12096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2379, d12096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2380 q = 1) (hb : d85721 q = 1) : d12097 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2380, d12097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2380, d12097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2381 q = 1) (hb : d85721 q = 1) : d12098 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2381, d12098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2381, d12098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2382 q = 1) (hb : d85721 q = 1) : d12099 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2382, d12099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2382, d12099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2383 q = 1) (hb : d85721 q = 1) : d12100 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2383, d12100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2383, d12100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15889 (p : Pattern) (ha : d2391 p = 1) (hb : d85721 p = 1) : d12108 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2378 q = 1) (hb : d85721 q = 1) : d12095 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2378, d12095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15887 q ha hb
    | true =>
      simp only [d2378, d12095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d2379 q = 1) (hb : d85721 q = 1) : d12096 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2379, d12096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2379, d12096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d2386 q = 1) (hb : d85721 q = 1) : d12103 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d2386, d12103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15866 q ha hb
    | true =>
      simp only [d2386, d12103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d2387 q = 1) (hb : d85721 q = 1) : d12104 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d2387, d12104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2387, d12104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2388 q = 1) (hb : d85721 q = 1) : d12105 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d2388, d12105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2388, d12105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2389 q = 1) (hb : d85721 q = 1) : d12106 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d2389, d12106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2389, d12106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d2390 q = 1) (hb : d85721 q = 1) : d12107 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d2390, d12107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2390, d12107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d2391 q = 1) (hb : d85721 q = 1) : d12108 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d2391, d12108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2391, d12108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15890 (p : Pattern) (ha : d5777 p = 1) (hb : d85721 p = 1) : d12141 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1 q = 1) (hb : d2351 q = 1) : d2351 q = 1 := by
    exact hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d2356 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2357 q = 1) (hb : d85721 q = 1) : d12080 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2357, d85721, d12080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d2357, d85721, d12080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d2358 q = 1) (hb : d85721 q = 1) : d12081 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2358, d12081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2358, d12081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d2359 q = 1) (hb : d85721 q = 1) : d12082 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2359, d12082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2359, d12082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1 q = 1) (hb : d2356 q = 1) : d2356 q = 1 := by
    exact hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d2366 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d2367 q = 1) (hb : d85721 q = 1) : d12084 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d2367, d85721, d12084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d2367, d85721, d12084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d2368 q = 1) (hb : d85721 q = 1) : d12085 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d2368, d12085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2368, d12085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d2369 q = 1) (hb : d85721 q = 1) : d12086 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d2369, d12086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2369, d12086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d2370 q = 1) (hb : d85721 q = 1) : d12087 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d2370, d12087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2370, d12087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d1 q = 1) (hb : d5770 q = 1) : d5770 q = 1 := by
    exact hb
  have h13 (q : Pattern) (ha : d0 q = 1) (hb : d5771 q = 1) : d0 q = 1 := by
    exact ha
  have h14 (q : Pattern) (ha : d5772 q = 1) (hb : d85721 q = 1) : d12136 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d5772, d85721, d12136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d5772, d85721, d12136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q hb ha
  have h15 (q : Pattern) (ha : d5773 q = 1) (hb : d85721 q = 1) : d12137 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d5773, d12137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5773, d12137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d5774 q = 1) (hb : d85721 q = 1) : d12138 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d5774, d12138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5774, d12138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d5775 q = 1) (hb : d85721 q = 1) : d12139 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d5775, d12139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d5775, d12139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h18 (q : Pattern) (ha : d5776 q = 1) (hb : d85721 q = 1) : d12140 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d5776, d12140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d5776, d12140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d5777 q = 1) (hb : d85721 q = 1) : d12141 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d5777, d12141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d5777, d12141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h19 p ha hb
theorem andIntro15891 (p : Pattern) (ha : d5783 p = 1) (hb : d85721 p = 1) : d12147 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d5778 q = 1) (hb : d85721 q = 1) : d12142 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d5778, d12142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15890 q ha hb
    | true =>
      simp only [d5778, d12142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d5779 q = 1) (hb : d85721 q = 1) : d12143 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d5779, d12143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d5779, d12143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d5780 q = 1) (hb : d85721 q = 1) : d12144 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d5780, d12144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5780, d12144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5781 q = 1) (hb : d85721 q = 1) : d12145 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d5781, d12145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5781, d12145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d5782 q = 1) (hb : d85721 q = 1) : d12146 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d5782, d12146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5782, d12146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d5783 q = 1) (hb : d85721 q = 1) : d12147 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d5783, d12147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d5783, d12147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15892 (p : Pattern) (ha : d74789 p = 1) (hb : d85721 p = 1) : d109049 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2392 q = 1) (hb : d85721 q = 1) : d12109 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d2392, d12109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15888 q ha hb
    | true =>
      simp only [d2392, d12109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15889 q ha hb
  have h2 (q : Pattern) (ha : d4586 q = 1) (hb : d85721 q = 1) : d109045 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d4586, d109045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d4586, d109045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d5784 q = 1) (hb : d85721 q = 1) : d12148 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d5784, d12148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15891 q ha hb
    | true =>
      simp only [d5784, d12148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d5785 q = 1) (hb : d85721 q = 1) : d12149 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d5785, d12149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d5785, d12149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74786 q = 1) (hb : d85721 q = 1) : d109046 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d74786, d109046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74786, d109046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74787 q = 1) (hb : d85721 q = 1) : d109047 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d74787, d109047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74787, d109047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74788 q = 1) (hb : d85721 q = 1) : d109048 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d74788, d109048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74788, d109048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d74789 q = 1) (hb : d85721 q = 1) : d109049 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d74789, d109049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74789, d109049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15893 (p : Pattern) (ha : d74795 p = 1) (hb : d85721 p = 1) : d109055 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2113 q = 1) (hb : d85721 q = 1) : d11939 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d11939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2113, d11939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15859 q ha hb
  have h2 (q : Pattern) (ha : d2114 q = 1) (hb : d85721 q = 1) : d11940 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d11940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2114, d11940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d2123 q = 1) (hb : d85721 q = 1) : d11949 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d11949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15859 q ha hb
    | true =>
      simp only [d2123, d11949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15862 q ha hb
  have h4 (q : Pattern) (ha : d2124 q = 1) (hb : d85721 q = 1) : d11950 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d11950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2124, d11950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d2125 q = 1) (hb : d85721 q = 1) : d11951 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d11951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2125, d11951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74774 q = 1) (hb : d85721 q = 1) : d109033 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74774, d109033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15877 q ha hb
    | true =>
      simp only [d74774, d109033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15884 q ha hb
  have h7 (q : Pattern) (ha : d2317 q = 1) (hb : d85721 q = 1) : d12063 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, d12063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15863 q ha hb
    | true =>
      simp only [d2317, d12063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15864 q ha hb
  have h8 (q : Pattern) (ha : d74775 q = 1) (hb : d85721 q = 1) : d109034 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74775, d109034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74775, d109034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74776 q = 1) (hb : d85721 q = 1) : d109035 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74776, d109035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74776, d109035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d74777 q = 1) (hb : d85721 q = 1) : d109036 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74777, d109036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74777, d109036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74781 q = 1) (hb : d85721 q = 1) : d109040 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74781, d109040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74781, d109040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15885 q ha hb
  have h12 (q : Pattern) (ha : d2326 q = 1) (hb : d85721 q = 1) : d12072 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d12072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2326, d12072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15865 q ha hb
  have h13 (q : Pattern) (ha : d74782 q = 1) (hb : d85721 q = 1) : d109041 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74782, d109041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d74782, d109041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74783 q = 1) (hb : d85721 q = 1) : d109042 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74783, d109042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d74783, d109042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d74784 q = 1) (hb : d85721 q = 1) : d109043 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74784, d109043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d74784, d109043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d74785 q = 1) (hb : d85721 q = 1) : d109044 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74785, d109044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74785, d109044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d74790 q = 1) (hb : d85721 q = 1) : d109050 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d74790, d109050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74790, d109050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15892 q ha hb
  have h18 (q : Pattern) (ha : d2459 q = 1) (hb : d85721 q = 1) : d12165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2459, d12165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d2459, d12165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15868 q ha hb
  have h19 (q : Pattern) (ha : d74791 q = 1) (hb : d85721 q = 1) : d109051 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d74791, d109051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d74791, d109051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d74792 q = 1) (hb : d85721 q = 1) : d109052 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d74792, d109052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d74792, d109052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h21 (q : Pattern) (ha : d74793 q = 1) (hb : d85721 q = 1) : d109053 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d74793, d109053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d74793, d109053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h22 (q : Pattern) (ha : d74794 q = 1) (hb : d85721 q = 1) : d109054 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d74794, d109054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d74794, d109054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d74795 q = 1) (hb : d85721 q = 1) : d109055 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d74795, d109055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d74795, d109055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro15894 (p : Pattern) (ha : d74801 p = 1) (hb : d85721 p = 1) : d109061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74796 q = 1) (hb : d85721 q = 1) : d109056 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d74796, d109056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74796, d109056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15893 q ha hb
  have h2 (q : Pattern) (ha : d74797 q = 1) (hb : d85721 q = 1) : d109057 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d74797, d109057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74797, d109057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d74798 q = 1) (hb : d85721 q = 1) : d109058 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d74798, d109058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74798, d109058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74799 q = 1) (hb : d85721 q = 1) : d109059 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d74799, d109059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74799, d109059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d74800 q = 1) (hb : d85721 q = 1) : d109060 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d74800, d109060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74800, d109060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74801 q = 1) (hb : d85721 q = 1) : d109061 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d74801, d109061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74801, d109061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15895 (p : Pattern) (ha : d74807 p = 1) (hb : d85721 p = 1) : d109067 p = 1 := by
  have h0 (q : Pattern) (ha : d74648 q = 1) (hb : d85721 q = 1) : d108896 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74648, d108896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15696 q ha hb
    | true =>
      simp only [d74648, d108896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15734 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d74685 q = 1) (hb : d85721 q = 1) : d108936 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74685, d108936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74685, d108936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15774 q ha hb
  have h3 (q : Pattern) (ha : d74686 q = 1) (hb : d85721 q = 1) : d108937 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74686, d108937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74686, d108937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d74723 q = 1) (hb : d85721 q = 1) : d108977 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74723, d108977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74723, d108977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15814 q ha hb
  have h5 (q : Pattern) (ha : d74724 q = 1) (hb : d85721 q = 1) : d108978 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74724, d108978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74724, d108978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d74725 q = 1) (hb : d85721 q = 1) : d108979 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74725, d108979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74725, d108979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d74762 q = 1) (hb : d85721 q = 1) : d109019 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74762, d109019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74762, d109019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15854 q ha hb
  have h8 (q : Pattern) (ha : d74763 q = 1) (hb : d85721 q = 1) : d109020 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74763, d109020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74763, d109020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d74764 q = 1) (hb : d85721 q = 1) : d109021 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74764, d109021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74764, d109021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74765 q = 1) (hb : d85721 q = 1) : d109022 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74765, d109022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74765, d109022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d74802 q = 1) (hb : d85721 q = 1) : d109062 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d74802, d109062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74802, d109062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15894 q ha hb
  have h12 (q : Pattern) (ha : d74803 q = 1) (hb : d85721 q = 1) : d109063 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d74803, d109063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74803, d109063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d74804 q = 1) (hb : d85721 q = 1) : d109064 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d74804, d109064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74804, d109064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d74805 q = 1) (hb : d85721 q = 1) : d109065 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d74805, d109065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74805, d109065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d74806 q = 1) (hb : d85721 q = 1) : d109066 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d74806, d109066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d74806, d109066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d74807 q = 1) (hb : d85721 q = 1) : d109067 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d74807, d109067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d74807, d109067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro15896 (p : Pattern) (ha : d74813 p = 1) (hb : d85721 p = 1) : d109073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74808 q = 1) (hb : d85721 q = 1) : d109068 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d74808, d109068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15895 q ha hb
    | true =>
      simp only [d74808, d109068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74809 q = 1) (hb : d85721 q = 1) : d109069 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d74809, d109069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74809, d109069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74810 q = 1) (hb : d85721 q = 1) : d109070 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d74810, d109070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74810, d109070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74811 q = 1) (hb : d85721 q = 1) : d109071 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d74811, d109071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74811, d109071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74812 q = 1) (hb : d85721 q = 1) : d109072 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d74812, d109072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74812, d109072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74813 q = 1) (hb : d85721 q = 1) : d109073 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d74813, d109073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74813, d109073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15897 (p : Pattern) (ha : d74819 p = 1) (hb : d85721 p = 1) : d109079 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74814 q = 1) (hb : d85721 q = 1) : d109074 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d74814, d109074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15896 q ha hb
    | true =>
      simp only [d74814, d109074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74815 q = 1) (hb : d85721 q = 1) : d109075 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d74815, d109075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74815, d109075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74816 q = 1) (hb : d85721 q = 1) : d109076 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d74816, d109076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74816, d109076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74817 q = 1) (hb : d85721 q = 1) : d109077 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d74817, d109077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74817, d109077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74818 q = 1) (hb : d85721 q = 1) : d109078 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d74818, d109078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74818, d109078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74819 q = 1) (hb : d85721 q = 1) : d109079 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d74819, d109079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74819, d109079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15898 (p : Pattern) (ha : d74825 p = 1) (hb : d85721 p = 1) : d109085 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74820 q = 1) (hb : d85721 q = 1) : d109080 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d74820, d109080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15897 q ha hb
    | true =>
      simp only [d74820, d109080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74821 q = 1) (hb : d85721 q = 1) : d109081 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d74821, d109081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74821, d109081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74822 q = 1) (hb : d85721 q = 1) : d109082 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d74822, d109082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74822, d109082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74823 q = 1) (hb : d85721 q = 1) : d109083 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d74823, d109083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74823, d109083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74824 q = 1) (hb : d85721 q = 1) : d109084 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d74824, d109084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74824, d109084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74825 q = 1) (hb : d85721 q = 1) : d109085 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d74825, d109085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74825, d109085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15899 (p : Pattern) (ha : d74831 p = 1) (hb : d107485 p = 1) : d109091 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d85721 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74826 q = 1) (hb : d85721 q = 1) : d109086 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d74826, d109086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15898 q ha hb
    | true =>
      simp only [d74826, d109086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74827 q = 1) (hb : d85721 q = 1) : d109087 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d74827, d109087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74827, d109087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d107483 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d74828 q = 1) (hb : d107484 q = 1) : d109088 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d74828, d107484, d109088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74828, d107484, d109088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d107484 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d74829 q = 1) (hb : d107484 q = 1) : d109089 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d74829, d109089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74829, d109089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d0 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d74830 q = 1) (hb : d107485 q = 1) : d109090 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d74830, d107485, d109090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d74830, d107485, d109090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107485 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d74831 q = 1) (hb : d107485 q = 1) : d109091 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d74831, d109091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d74831, d109091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro15900 (p : Pattern) (ha : d74837 p = 1) (hb : d107485 p = 1) : d109097 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107485 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74832 q = 1) (hb : d107485 q = 1) : d109092 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d74832, d109092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15899 q ha hb
    | true =>
      simp only [d74832, d109092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74833 q = 1) (hb : d107485 q = 1) : d109093 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d74833, d109093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74833, d109093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74834 q = 1) (hb : d107485 q = 1) : d109094 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d74834, d109094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74834, d109094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74835 q = 1) (hb : d107485 q = 1) : d109095 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d74835, d109095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74835, d109095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74836 q = 1) (hb : d107485 q = 1) : d109096 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d74836, d109096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74836, d109096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74837 q = 1) (hb : d107485 q = 1) : d109097 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d74837, d109097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74837, d109097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15901 (p : Pattern) (ha : d74843 p = 1) (hb : d107485 p = 1) : d109103 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107485 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74838 q = 1) (hb : d107485 q = 1) : d109098 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d74838, d109098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15900 q ha hb
    | true =>
      simp only [d74838, d109098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74839 q = 1) (hb : d107485 q = 1) : d109099 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d74839, d109099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74839, d109099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74840 q = 1) (hb : d107485 q = 1) : d109100 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d74840, d109100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74840, d109100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74841 q = 1) (hb : d107485 q = 1) : d109101 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d74841, d109101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74841, d109101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74842 q = 1) (hb : d107485 q = 1) : d109102 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d74842, d109102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74842, d109102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74843 q = 1) (hb : d107485 q = 1) : d109103 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d74843, d109103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74843, d109103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15902 (p : Pattern) (ha : d74849 p = 1) (hb : d107485 p = 1) : d109109 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d107485 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d74844 q = 1) (hb : d107485 q = 1) : d109104 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d74844, d109104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15901 q ha hb
    | true =>
      simp only [d74844, d109104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d74845 q = 1) (hb : d107485 q = 1) : d109105 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d74845, d109105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d74845, d109105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d74846 q = 1) (hb : d107485 q = 1) : d109106 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d74846, d109106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d74846, d109106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d74847 q = 1) (hb : d107485 q = 1) : d109107 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d74847, d109107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d74847, d109107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d74848 q = 1) (hb : d107485 q = 1) : d109108 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d74848, d109108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d74848, d109108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d74849 q = 1) (hb : d107485 q = 1) : d109109 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d74849, d109109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d74849, d109109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15903 (p : Pattern) (ha : d10654 p = 1) (hb : d107491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10649 q = 1) (hb : d107486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10650 q = 1) (hb : d107487 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10651 q = 1) (hb : d107488 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h7 (q : Pattern) (ha : d10652 q = 1) (hb : d107489 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10652, d107489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10652, d107489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d34 q = 1) (hb : d51886 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d34, d51886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10653 q = 1) (hb : d107490 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10653, d107490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10653, d107490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10654 q = 1) (hb : d107491 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10654, d107491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10654, d107491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro15904 (p : Pattern) (ha : d10660 p = 1) (hb : d107497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d107492 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15903 q ha hb
    | true =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d107493 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d107494 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10658 q = 1) (hb : d107495 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d107495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10658, d107495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10659 q = 1) (hb : d107496 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10659, d107496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10659, d107496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10660 q = 1) (hb : d107497 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10660, d107497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10660, d107497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15905 (p : Pattern) (ha : d107503 p = 1) (hb : d108784 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d10661 q = 1) (hb : d107498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d107498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15904 q ha hb
    | true =>
      simp only [d10661, d107498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107499 q = 1) (hb : d108780 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107499, d108780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d107499, d108780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d107500 q = 1) (hb : d108781 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107500, d108781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107500, d108781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d107501 q = 1) (hb : d108782 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107501, d108782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107501, d108782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107502 q = 1) (hb : d108783 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107502, d108783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107502, d108783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107503 q = 1) (hb : d108784 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107503, d108784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107503, d108784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro15906 (p : Pattern) (ha : d10667 p = 1) (hb : d107504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d107492 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15903 q ha hb
    | true =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d107493 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d107494 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10658 q = 1) (hb : d107495 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d107495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10658, d107495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10659 q = 1) (hb : d107496 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10659, d107496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10659, d107496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10667 q = 1) (hb : d107504 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10667, d107504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10667, d107504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15907 (p : Pattern) (ha : d107510 p = 1) (hb : d108789 p = 1) : d0 p = 1 := by
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
  have h8 (q : Pattern) (ha : d10661 q = 1) (hb : d107498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d107498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15904 q ha hb
    | true =>
      simp only [d10661, d107498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107499 q = 1) (hb : d108780 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107499, d108780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d107499, d108780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h13 (q : Pattern) (ha : d107500 q = 1) (hb : d108781 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107500, d108781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107500, d108781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d107501 q = 1) (hb : d108782 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107501, d108782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107501, d108782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107502 q = 1) (hb : d108783 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107502, d108783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107502, d108783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h23 (q : Pattern) (ha : d10668 q = 1) (hb : d107505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d107505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15906 q ha hb
    | true =>
      simp only [d10668, d107505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d107506 q = 1) (hb : d108785 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107506, d108785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d107506, d108785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h28 (q : Pattern) (ha : d107507 q = 1) (hb : d108786 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107507, d108786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d107507, d108786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d107508 q = 1) (hb : d108787 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107508, d108787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d107508, d108787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d107509 q = 1) (hb : d108788 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107509, d108788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d107509, d108788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d107510 q = 1) (hb : d108789 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107510, d108789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107510, d108789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro15908 (p : Pattern) (ha : d107517 p = 1) (hb : d108796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10668 q = 1) (hb : d107505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d107505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15906 q ha hb
    | true =>
      simp only [d10668, d107505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51902 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107506 q = 1) (hb : d108785 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107506, d108785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107506, d108785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d107507 q = 1) (hb : d108786 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107507, d108786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107507, d108786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107515 q = 1) (hb : d108794 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107515, d108794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107515, d108794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107516 q = 1) (hb : d108795 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107516, d108795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107516, d108795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107517 q = 1) (hb : d108796 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107517, d108796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107517, d108796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro15909 (p : Pattern) (ha : d10691 p = 1) (hb : d107528 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10686 q = 1) (hb : d107523 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10687 q = 1) (hb : d107524 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10688 q = 1) (hb : d107525 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h7 (q : Pattern) (ha : d10689 q = 1) (hb : d107526 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10689, d107526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10689, d107526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75 q = 1) (hb : d51927 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d75, d51927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10690 q = 1) (hb : d107527 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10690, d107527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10690, d107527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10691 q = 1) (hb : d107528 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10691, d107528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10691, d107528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro15910 (p : Pattern) (ha : d10697 p = 1) (hb : d107534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10692 q = 1) (hb : d107529 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d107529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15909 q ha hb
    | true =>
      simp only [d10692, d107529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10693 q = 1) (hb : d107530 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d107530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d107530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d78 q = 1) (hb : d51930 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro11 q ha hb
    | true =>
      simp only [d78, d51930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d79 q = 1) (hb : d51931 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d79, d51931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10694 q = 1) (hb : d107531 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10694, d107531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10694, d107531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10695 q = 1) (hb : d107532 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10695, d107532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10695, d107532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10696 q = 1) (hb : d107533 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10696, d107533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10696, d107533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10697 q = 1) (hb : d107534 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10697, d107534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10697, d107534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15911 (p : Pattern) (ha : d107540 p = 1) (hb : d108806 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10698 q = 1) (hb : d107535 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10698, d107535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15910 q ha hb
    | true =>
      simp only [d10698, d107535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d51936 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107536 q = 1) (hb : d108802 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107536, d108802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107536, d108802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h6 (q : Pattern) (ha : d107537 q = 1) (hb : d108803 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107537, d108803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107537, d108803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107538 q = 1) (hb : d108804 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107538, d108804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107538, d108804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107539 q = 1) (hb : d108805 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107539, d108805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107539, d108805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107540 q = 1) (hb : d108806 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107540, d108806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107540, d108806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro15912 (p : Pattern) (ha : d107546 p = 1) (hb : d108812 p = 1) : d0 p = 1 := by
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
  have h6 (q : Pattern) (ha : d107511 q = 1) (hb : d108790 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107511, d108790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15905 q ha hb
    | true =>
      simp only [d107511, d108790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15907 q ha hb
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
  have h8 (q : Pattern) (ha : d107512 q = 1) (hb : d108791 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107512, d108791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107512, d108791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d107513 q = 1) (hb : d108792 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107513, d108792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107513, d108792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d107514 q = 1) (hb : d108793 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107514, d108793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d107514, d108793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107518 q = 1) (hb : d108797 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107518, d108797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107518, d108797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15908 q ha hb
  have h12 (q : Pattern) (ha : d107519 q = 1) (hb : d108798 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107519, d108798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107519, d108798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d107520 q = 1) (hb : d108799 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107520, d108799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d107520, d108799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h14 (q : Pattern) (ha : d107521 q = 1) (hb : d108800 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107521, d108800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107521, d108800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107522 q = 1) (hb : d108801 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107522, d108801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107522, d108801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107541 q = 1) (hb : d108807 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107541, d108807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107541, d108807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15911 q ha hb
  have h17 (q : Pattern) (ha : d107542 q = 1) (hb : d108808 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107542, d108808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d107542, d108808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h18 (q : Pattern) (ha : d107543 q = 1) (hb : d108809 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107543, d108809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107543, d108809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d107544 q = 1) (hb : d108810 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107544, d108810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
    | true =>
      simp only [d107544, d108810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h20 (q : Pattern) (ha : d107545 q = 1) (hb : d108811 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107545, d108811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107545, d108811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d107546 q = 1) (hb : d108812 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107546, d108812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107546, d108812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  exact h21 p ha hb
theorem andIntro15913 (p : Pattern) (ha : d10719 p = 1) (hb : d107556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10661 q = 1) (hb : d107498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d107498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15904 q ha hb
    | true =>
      simp only [d10661, d107498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d10715 q = 1) (hb : d107552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d107552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d107552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10716 q = 1) (hb : d107553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d107553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10716, d107553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10717 q = 1) (hb : d107554 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d107554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d107554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10718 q = 1) (hb : d107555 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d107555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d107555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10719 q = 1) (hb : d107556 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10719, d107556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10719, d107556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15914 (p : Pattern) (ha : d10726 p = 1) (hb : d107563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10661 q = 1) (hb : d107498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d107498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15904 q ha hb
    | true =>
      simp only [d10661, d107498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d10715 q = 1) (hb : d107552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d107552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d107552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10716 q = 1) (hb : d107553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d107553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10716, d107553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10717 q = 1) (hb : d107554 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d107554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d107554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10718 q = 1) (hb : d107555 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d107555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d107555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10668 q = 1) (hb : d107505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d107505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15906 q ha hb
    | true =>
      simp only [d10668, d107505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q ha hb
  have h7 (q : Pattern) (ha : d10722 q = 1) (hb : d107559 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10722, d107559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10722, d107559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10723 q = 1) (hb : d107560 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10723, d107560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10723, d107560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10724 q = 1) (hb : d107561 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10724, d107561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10724, d107561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10725 q = 1) (hb : d107562 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10725, d107562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10725, d107562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10726 q = 1) (hb : d107563 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10726, d107563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10726, d107563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15915 (p : Pattern) (ha : d10801 p = 1) (hb : d107623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10661 q = 1) (hb : d107498 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10661, d107498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15904 q ha hb
    | true =>
      simp only [d10661, d107498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
  have h2 (q : Pattern) (ha : d10715 q = 1) (hb : d107552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10715, d107552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10715, d107552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10716 q = 1) (hb : d107553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10716, d107553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10716, d107553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10717 q = 1) (hb : d107554 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10717, d107554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10717, d107554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10718 q = 1) (hb : d107555 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10718, d107555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10718, d107555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
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
  have h11 (q : Pattern) (ha : d10801 q = 1) (hb : d107623 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10801, d107623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10801, d107623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15916 (p : Pattern) (ha : d10731 p = 1) (hb : d107568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d107492 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15903 q ha hb
    | true =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d107493 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d107494 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10658 q = 1) (hb : d107495 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d107495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10658, d107495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10730 q = 1) (hb : d107567 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10730, d107567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10730, d107567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10731 q = 1) (hb : d107568 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10731, d107568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10731, d107568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15917 (p : Pattern) (ha : d10738 p = 1) (hb : d107575 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d107492 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15903 q ha hb
    | true =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d107493 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d107494 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10736 q = 1) (hb : d107573 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10736, d107573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10736, d107573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10737 q = 1) (hb : d107574 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10737, d107574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10737, d107574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10738 q = 1) (hb : d107575 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10738, d107575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10738, d107575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15918 (p : Pattern) (ha : d10747 p = 1) (hb : d107584 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10742 q = 1) (hb : d107579 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d107579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d10742, d107579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10743 q = 1) (hb : d107580 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d107580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d107580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10744 q = 1) (hb : d107581 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d107581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d107581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10649 q = 1) (hb : d107486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10650 q = 1) (hb : d107487 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10651 q = 1) (hb : d107488 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10745 q = 1) (hb : d107582 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d107582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10745, d107582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10652 q = 1) (hb : d107489 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10652, d107489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10652, d107489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10746 q = 1) (hb : d107583 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10746, d107583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10746, d107583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10747 q = 1) (hb : d107584 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10747, d107584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10747, d107584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro15919 (p : Pattern) (ha : d10753 p = 1) (hb : d107590 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10748 q = 1) (hb : d107585 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10748, d107585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15918 q ha hb
    | true =>
      simp only [d10748, d107585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10749 q = 1) (hb : d107586 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10749, d107586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10749, d107586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10655 q = 1) (hb : d107492 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15903 q ha hb
    | true =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10656 q = 1) (hb : d107493 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10750 q = 1) (hb : d107587 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10750, d107587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10750, d107587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10751 q = 1) (hb : d107588 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10751, d107588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10751, d107588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10752 q = 1) (hb : d107589 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10752, d107589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10752, d107589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10753 q = 1) (hb : d107590 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10753, d107590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10753, d107590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15920 (p : Pattern) (ha : d10772 p = 1) (hb : d107596 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d107492 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15903 q ha hb
    | true =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d107493 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10769 q = 1) (hb : d107593 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10769, d107593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10769, d107593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10770 q = 1) (hb : d107594 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10770, d107594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10770, d107594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10771 q = 1) (hb : d107595 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10771, d107595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10771, d107595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10772 q = 1) (hb : d107596 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10772, d107596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10772, d107596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15921 (p : Pattern) (ha : d107602 p = 1) (hb : d108822 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10732 q = 1) (hb : d107569 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10732, d107569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15916 q ha hb
    | true =>
      simp only [d10732, d107569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d10733 q = 1) (hb : d107570 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10733, d107570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10733, d107570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10734 q = 1) (hb : d107571 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10734, d107571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10734, d107571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10735 q = 1) (hb : d107572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10735, d107572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10735, d107572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10739 q = 1) (hb : d107576 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10739, d107576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15917 q ha hb
    | true =>
      simp only [d10739, d107576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d10740 q = 1) (hb : d107577 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10740, d107577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10740, d107577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10741 q = 1) (hb : d107578 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10741, d107578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10741, d107578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10754 q = 1) (hb : d107591 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10754, d107591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15919 q ha hb
    | true =>
      simp only [d10754, d107591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15904 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107498 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107592 q = 1) (hb : d108818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107592, d108818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d107592, d108818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10773 q = 1) (hb : d107597 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10773, d107597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15920 q ha hb
    | true =>
      simp only [d10773, d107597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10774 q = 1) (hb : d107598 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10774, d107598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10774, d107598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d107599 q = 1) (hb : d108819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107599, d108819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107599, d108819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d107600 q = 1) (hb : d108820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107600, d108820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107600, d108820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107601 q = 1) (hb : d108821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107601, d108821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107601, d108821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107602 q = 1) (hb : d108822 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107602, d108822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107602, d108822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro15922 (p : Pattern) (ha : d10779 p = 1) (hb : d107603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d107492 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15903 q ha hb
    | true =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d107493 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d107494 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10658 q = 1) (hb : d107495 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10658, d107495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10658, d107495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10730 q = 1) (hb : d107567 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10730, d107567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10730, d107567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10779 q = 1) (hb : d107603 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10779, d107603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10779, d107603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15923 (p : Pattern) (ha : d10784 p = 1) (hb : d107608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d107492 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15903 q ha hb
    | true =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d107493 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10657 q = 1) (hb : d107494 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10657, d107494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10736 q = 1) (hb : d107573 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10736, d107573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10736, d107573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10737 q = 1) (hb : d107574 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10737, d107574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10737, d107574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10784 q = 1) (hb : d107608 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10784, d107608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10784, d107608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15924 (p : Pattern) (ha : d10788 p = 1) (hb : d107612 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10748 q = 1) (hb : d107585 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10748, d107585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15918 q ha hb
    | true =>
      simp only [d10748, d107585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10749 q = 1) (hb : d107586 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10749, d107586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10749, d107586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10655 q = 1) (hb : d107492 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15903 q ha hb
    | true =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10656 q = 1) (hb : d107493 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10750 q = 1) (hb : d107587 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10750, d107587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10750, d107587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10751 q = 1) (hb : d107588 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10751, d107588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10751, d107588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10752 q = 1) (hb : d107589 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10752, d107589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10752, d107589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10788 q = 1) (hb : d107612 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10788, d107612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10788, d107612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15925 (p : Pattern) (ha : d10793 p = 1) (hb : d107615 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10655 q = 1) (hb : d107492 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15903 q ha hb
    | true =>
      simp only [d10655, d107492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10656 q = 1) (hb : d107493 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10656, d107493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10769 q = 1) (hb : d107593 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10769, d107593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10769, d107593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10770 q = 1) (hb : d107594 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10770, d107594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10770, d107594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10771 q = 1) (hb : d107595 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10771, d107595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10771, d107595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10793 q = 1) (hb : d107615 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10793, d107615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10793, d107615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15926 (p : Pattern) (ha : d107621 p = 1) (hb : d108827 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10732 q = 1) (hb : d107569 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10732, d107569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15916 q ha hb
    | true =>
      simp only [d10732, d107569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q ha hb
  have h2 (q : Pattern) (ha : d10733 q = 1) (hb : d107570 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10733, d107570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10733, d107570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10734 q = 1) (hb : d107571 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10734, d107571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10734, d107571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10735 q = 1) (hb : d107572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10735, d107572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10735, d107572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10739 q = 1) (hb : d107576 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10739, d107576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15917 q ha hb
    | true =>
      simp only [d10739, d107576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q ha hb
  have h6 (q : Pattern) (ha : d10740 q = 1) (hb : d107577 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10740, d107577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10740, d107577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10741 q = 1) (hb : d107578 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10741, d107578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10741, d107578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10754 q = 1) (hb : d107591 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10754, d107591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15919 q ha hb
    | true =>
      simp only [d10754, d107591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15904 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107498 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107592 q = 1) (hb : d108818 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107592, d108818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d107592, d108818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10773 q = 1) (hb : d107597 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10773, d107597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15920 q ha hb
    | true =>
      simp only [d10773, d107597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10774 q = 1) (hb : d107598 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10774, d107598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10774, d107598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d107599 q = 1) (hb : d108819 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107599, d108819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107599, d108819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d107600 q = 1) (hb : d108820 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107600, d108820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107600, d108820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107601 q = 1) (hb : d108821 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107601, d108821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107601, d108821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10780 q = 1) (hb : d107604 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10780, d107604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15922 q ha hb
    | true =>
      simp only [d10780, d107604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q ha hb
  have h17 (q : Pattern) (ha : d10781 q = 1) (hb : d107605 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10781, d107605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10781, d107605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10782 q = 1) (hb : d107606 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10782, d107606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10782, d107606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d10783 q = 1) (hb : d107607 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10783, d107607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10783, d107607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10785 q = 1) (hb : d107609 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10785, d107609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15923 q ha hb
    | true =>
      simp only [d10785, d107609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q ha hb
  have h21 (q : Pattern) (ha : d10786 q = 1) (hb : d107610 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10786, d107610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10786, d107610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d10787 q = 1) (hb : d107611 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10787, d107611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d10787, d107611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d10789 q = 1) (hb : d107613 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10789, d107613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15924 q ha hb
    | true =>
      simp only [d10789, d107613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15906 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d107505 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d107614 q = 1) (hb : d108823 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107614, d108823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d107614, d108823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d10794 q = 1) (hb : d107616 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10794, d107616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15925 q ha hb
    | true =>
      simp only [d10794, d107616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d10795 q = 1) (hb : d107617 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10795, d107617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d10795, d107617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d107618 q = 1) (hb : d108824 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107618, d108824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d107618, d108824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d107619 q = 1) (hb : d108825 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107619, d108825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d107619, d108825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d107620 q = 1) (hb : d108826 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107620, d108826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d107620, d108826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d107621 q = 1) (hb : d108827 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107621, d108827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107621, d108827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro15927 (p : Pattern) (ha : d107630 p = 1) (hb : d108834 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10789 q = 1) (hb : d107613 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10789, d107613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15924 q ha hb
    | true =>
      simp only [d10789, d107613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15906 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107505 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107614 q = 1) (hb : d108823 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107614, d108823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107614, d108823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d10794 q = 1) (hb : d107616 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10794, d107616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15925 q ha hb
    | true =>
      simp only [d10794, d107616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10795 q = 1) (hb : d107617 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10795, d107617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10795, d107617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d107618 q = 1) (hb : d108824 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107618, d108824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107618, d108824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107628 q = 1) (hb : d108832 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107628, d108832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107628, d108832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107629 q = 1) (hb : d108833 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107629, d108833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107629, d108833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107630 q = 1) (hb : d108834 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107630, d108834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107630, d108834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro15928 (p : Pattern) (ha : d10819 p = 1) (hb : d107641 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10814 q = 1) (hb : d107636 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d107636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d10814, d107636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10815 q = 1) (hb : d107637 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d107637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10815, d107637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10816 q = 1) (hb : d107638 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d107638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10816, d107638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10686 q = 1) (hb : d107523 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10687 q = 1) (hb : d107524 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10688 q = 1) (hb : d107525 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10817 q = 1) (hb : d107639 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d107639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10817, d107639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10689 q = 1) (hb : d107526 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10689, d107526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10689, d107526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10818 q = 1) (hb : d107640 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10818, d107640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10818, d107640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10819 q = 1) (hb : d107641 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10819, d107641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10819, d107641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro15929 (p : Pattern) (ha : d10825 p = 1) (hb : d107647 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10820 q = 1) (hb : d107642 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10820, d107642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15928 q ha hb
    | true =>
      simp only [d10820, d107642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10821 q = 1) (hb : d107643 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10821, d107643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10821, d107643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10692 q = 1) (hb : d107529 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d107529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15909 q ha hb
    | true =>
      simp only [d10692, d107529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10693 q = 1) (hb : d107530 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d107530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d107530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10822 q = 1) (hb : d107644 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10822, d107644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10822, d107644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10823 q = 1) (hb : d107645 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10823, d107645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10823, d107645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10824 q = 1) (hb : d107646 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10824, d107646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10824, d107646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10825 q = 1) (hb : d107647 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10825, d107647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10825, d107647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15930 (p : Pattern) (ha : d10844 p = 1) (hb : d107653 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10692 q = 1) (hb : d107529 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10692, d107529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15909 q ha hb
    | true =>
      simp only [d10692, d107529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10693 q = 1) (hb : d107530 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10693, d107530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10693, d107530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10841 q = 1) (hb : d107650 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10841, d107650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10841, d107650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10842 q = 1) (hb : d107651 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10842, d107651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10842, d107651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10843 q = 1) (hb : d107652 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10843, d107652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10843, d107652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10844 q = 1) (hb : d107653 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10844, d107653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10844, d107653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15931 (p : Pattern) (ha : d107659 p = 1) (hb : d108844 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10826 q = 1) (hb : d107648 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10826, d107648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15929 q ha hb
    | true =>
      simp only [d10826, d107648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15910 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107535 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107649 q = 1) (hb : d108840 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107649, d108840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107649, d108840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d10845 q = 1) (hb : d107654 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10845, d107654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15930 q ha hb
    | true =>
      simp only [d10845, d107654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10846 q = 1) (hb : d107655 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10846, d107655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10846, d107655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d107656 q = 1) (hb : d108841 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107656, d108841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107656, d108841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107657 q = 1) (hb : d108842 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107657, d108842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107657, d108842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107658 q = 1) (hb : d108843 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107658, d108843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107658, d108843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107659 q = 1) (hb : d108844 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107659, d108844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107659, d108844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro15932 (p : Pattern) (ha : d107665 p = 1) (hb : d108850 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10720 q = 1) (hb : d107557 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10720, d107557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10720, d107557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15913 q ha hb
  have h2 (q : Pattern) (ha : d10721 q = 1) (hb : d107558 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10721, d107558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10721, d107558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10727 q = 1) (hb : d107564 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10727, d107564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15913 q ha hb
    | true =>
      simp only [d10727, d107564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15914 q ha hb
  have h4 (q : Pattern) (ha : d10728 q = 1) (hb : d107565 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10728, d107565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10728, d107565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10729 q = 1) (hb : d107566 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10729, d107566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10729, d107566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107622 q = 1) (hb : d108828 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107622, d108828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15921 q ha hb
    | true =>
      simp only [d107622, d108828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15926 q ha hb
  have h7 (q : Pattern) (ha : d10802 q = 1) (hb : d107624 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10802, d107624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15915 q ha hb
    | true =>
      simp only [d10802, d107624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q ha hb
  have h8 (q : Pattern) (ha : d107625 q = 1) (hb : d108829 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107625, d108829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107625, d108829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d107626 q = 1) (hb : d108830 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107626, d108830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107626, d108830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d107627 q = 1) (hb : d108831 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107627, d108831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d107627, d108831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107631 q = 1) (hb : d108835 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107631, d108835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107631, d108835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15927 q ha hb
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
  have h13 (q : Pattern) (ha : d107632 q = 1) (hb : d108836 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107632, d108836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107632, d108836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d107633 q = 1) (hb : d108837 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107633, d108837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107633, d108837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107634 q = 1) (hb : d108838 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107634, d108838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d107634, d108838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d107635 q = 1) (hb : d108839 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107635, d108839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107635, d108839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107660 q = 1) (hb : d108845 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107660, d108845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107660, d108845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15931 q ha hb
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
  have h19 (q : Pattern) (ha : d107661 q = 1) (hb : d108846 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107661, d108846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107661, d108846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d107662 q = 1) (hb : d108847 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107662, d108847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107662, d108847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d107663 q = 1) (hb : d108848 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107663, d108848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d107663, d108848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d107664 q = 1) (hb : d108849 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107664, d108849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d107664, d108849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107665 q = 1) (hb : d108850 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107665, d108850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d107665, d108850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro15933 (p : Pattern) (ha : d107671 p = 1) (hb : d108856 p = 1) : d0 p = 1 := by
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
  have h5 (q : Pattern) (ha : d107547 q = 1) (hb : d108813 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107547, d108813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107547, d108813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15912 q ha hb
  have h6 (q : Pattern) (ha : d107548 q = 1) (hb : d108814 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107548, d108814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107548, d108814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d107549 q = 1) (hb : d108815 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107549, d108815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107549, d108815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107550 q = 1) (hb : d108816 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107550, d108816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107550, d108816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107551 q = 1) (hb : d108817 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107551, d108817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107551, d108817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d107666 q = 1) (hb : d108851 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107666, d108851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107666, d108851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15932 q ha hb
  have h11 (q : Pattern) (ha : d107667 q = 1) (hb : d108852 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107667, d108852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107667, d108852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d107668 q = 1) (hb : d108853 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107668, d108853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107668, d108853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d107669 q = 1) (hb : d108854 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107669, d108854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107669, d108854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d107670 q = 1) (hb : d108855 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107670, d108855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107670, d108855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107671 q = 1) (hb : d108856 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d107671, d108856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d107671, d108856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro15934 (p : Pattern) (ha : d10865 p = 1) (hb : d107674 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10742 q = 1) (hb : d107579 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d107579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d10742, d107579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10743 q = 1) (hb : d107580 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d107580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d107580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10744 q = 1) (hb : d107581 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d107581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d107581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10649 q = 1) (hb : d107486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10650 q = 1) (hb : d107487 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10651 q = 1) (hb : d107488 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10745 q = 1) (hb : d107582 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d107582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10745, d107582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10863 q = 1) (hb : d107672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10863, d107672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10863, d107672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10864 q = 1) (hb : d107673 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10864, d107673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10864, d107673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10865 q = 1) (hb : d107674 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10865, d107674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10865, d107674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro15935 (p : Pattern) (ha : d10869 p = 1) (hb : d107678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10649 q = 1) (hb : d107486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10650 q = 1) (hb : d107487 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10651 q = 1) (hb : d107488 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10863 q = 1) (hb : d107672 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10863, d107672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10863, d107672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10868 q = 1) (hb : d107677 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10868, d107677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10868, d107677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10869 q = 1) (hb : d107678 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10869, d107678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10869, d107678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15936 (p : Pattern) (ha : d10875 p = 1) (hb : d107684 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d107675 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15934 q ha hb
    | true =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d107676 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d107679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15935 q ha hb
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d107680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d107681 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d107682 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d107682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d107682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10874 q = 1) (hb : d107683 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10874, d107683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10874, d107683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10875 q = 1) (hb : d107684 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10875, d107684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10875, d107684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15937 (p : Pattern) (ha : d10879 p = 1) (hb : d107688 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d107679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15935 q ha hb
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d107680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d107685 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10877 q = 1) (hb : d107686 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d107686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10877, d107686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10878 q = 1) (hb : d107687 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10878, d107687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10878, d107687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10879 q = 1) (hb : d107688 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10879, d107688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10879, d107688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15938 (p : Pattern) (ha : d10885 p = 1) (hb : d107694 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10880 q = 1) (hb : d107689 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d107689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15936 q ha hb
    | true =>
      simp only [d10880, d107689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15937 q ha hb
  have h2 (q : Pattern) (ha : d10881 q = 1) (hb : d107690 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d107690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d107690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10882 q = 1) (hb : d107691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d107691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10882, d107691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10883 q = 1) (hb : d107692 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d107692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d107692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10884 q = 1) (hb : d107693 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d107693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d107693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10885 q = 1) (hb : d107694 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10885, d107694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10885, d107694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15939 (p : Pattern) (ha : d10888 p = 1) (hb : d107697 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d107675 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15934 q ha hb
    | true =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d107676 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d107679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15935 q ha hb
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d107680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d107681 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d107682 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d107682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d107682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10874 q = 1) (hb : d107683 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10874, d107683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10874, d107683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10888 q = 1) (hb : d107697 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10888, d107697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10888, d107697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15940 (p : Pattern) (ha : d10889 p = 1) (hb : d107698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d107679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15935 q ha hb
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d107680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d107685 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10877 q = 1) (hb : d107686 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d107686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10877, d107686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10878 q = 1) (hb : d107687 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10878, d107687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10878, d107687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10889 q = 1) (hb : d107698 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10889, d107698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10889, d107698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15941 (p : Pattern) (ha : d10895 p = 1) (hb : d107704 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10880 q = 1) (hb : d107689 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d107689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15936 q ha hb
    | true =>
      simp only [d10880, d107689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15937 q ha hb
  have h2 (q : Pattern) (ha : d10881 q = 1) (hb : d107690 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d107690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d107690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10882 q = 1) (hb : d107691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d107691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10882, d107691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10883 q = 1) (hb : d107692 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d107692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d107692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10884 q = 1) (hb : d107693 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d107693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d107693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10890 q = 1) (hb : d107699 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10890, d107699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15939 q ha hb
    | true =>
      simp only [d10890, d107699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15940 q ha hb
  have h7 (q : Pattern) (ha : d10891 q = 1) (hb : d107700 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10891, d107700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10891, d107700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10892 q = 1) (hb : d107701 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10892, d107701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10892, d107701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10893 q = 1) (hb : d107702 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10893, d107702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10893, d107702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10894 q = 1) (hb : d107703 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10894, d107703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10894, d107703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10895 q = 1) (hb : d107704 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10895, d107704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10895, d107704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15942 (p : Pattern) (ha : d10992 p = 1) (hb : d107776 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10880 q = 1) (hb : d107689 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10880, d107689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15936 q ha hb
    | true =>
      simp only [d10880, d107689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15937 q ha hb
  have h2 (q : Pattern) (ha : d10881 q = 1) (hb : d107690 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10881, d107690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10881, d107690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10882 q = 1) (hb : d107691 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10882, d107691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10882, d107691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10883 q = 1) (hb : d107692 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10883, d107692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10883, d107692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10884 q = 1) (hb : d107693 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10884, d107693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10884, d107693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10987 q = 1) (hb : d107771 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10987, d107771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15937 q ha hb
    | true =>
      simp only [d10987, d107771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10988 q = 1) (hb : d107772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10988, d107772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10988, d107772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10989 q = 1) (hb : d107773 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10989, d107773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10989, d107773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10990 q = 1) (hb : d107774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10990, d107774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10990, d107774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10991 q = 1) (hb : d107775 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10991, d107775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10991, d107775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10992 q = 1) (hb : d107776 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10992, d107776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10992, d107776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15943 (p : Pattern) (ha : d10998 p = 1) (hb : d107782 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10987 q = 1) (hb : d107771 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10987, d107771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15937 q ha hb
    | true =>
      simp only [d10987, d107771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10988 q = 1) (hb : d107772 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10988, d107772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10988, d107772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10989 q = 1) (hb : d107773 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10989, d107773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10989, d107773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10990 q = 1) (hb : d107774 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10990, d107774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10990, d107774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10991 q = 1) (hb : d107775 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10991, d107775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10991, d107775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10993 q = 1) (hb : d107777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10993, d107777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15940 q ha hb
    | true =>
      simp only [d10993, d107777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10994 q = 1) (hb : d107778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10994, d107778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10994, d107778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10995 q = 1) (hb : d107779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10995, d107779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10995, d107779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10996 q = 1) (hb : d107780 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10996, d107780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10996, d107780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10997 q = 1) (hb : d107781 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10997, d107781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10997, d107781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10998 q = 1) (hb : d107782 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d10998, d107782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10998, d107782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15944 (p : Pattern) (ha : d11007 p = 1) (hb : d107791 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10993 q = 1) (hb : d107777 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10993, d107777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15940 q ha hb
    | true =>
      simp only [d10993, d107777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10994 q = 1) (hb : d107778 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10994, d107778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10994, d107778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10995 q = 1) (hb : d107779 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10995, d107779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10995, d107779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10996 q = 1) (hb : d107780 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10996, d107780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10996, d107780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10997 q = 1) (hb : d107781 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10997, d107781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10997, d107781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11007 q = 1) (hb : d107791 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11007, d107791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11007, d107791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15945 (p : Pattern) (ha : d11031 p = 1) (hb : d107815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10686 q = 1) (hb : d107523 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10687 q = 1) (hb : d107524 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10688 q = 1) (hb : d107525 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11021 q = 1) (hb : d107805 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11021, d107805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11021, d107805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11030 q = 1) (hb : d107814 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11030, d107814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11030, d107814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11031 q = 1) (hb : d107815 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11031, d107815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11031, d107815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15946 (p : Pattern) (ha : d11076 p = 1) (hb : d107826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11032 q = 1) (hb : d107816 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11032, d107816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15945 q ha hb
    | true =>
      simp only [d11032, d107816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11033 q = 1) (hb : d107817 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11033, d107817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11033, d107817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11073 q = 1) (hb : d107823 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11073, d107823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11073, d107823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11074 q = 1) (hb : d107824 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11074, d107824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11074, d107824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11075 q = 1) (hb : d107825 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11075, d107825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11075, d107825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11076 q = 1) (hb : d107826 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11076, d107826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11076, d107826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15947 (p : Pattern) (ha : d11082 p = 1) (hb : d107845 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11077 q = 1) (hb : d107840 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11077, d107840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15946 q ha hb
    | true =>
      simp only [d11077, d107840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11078 q = 1) (hb : d107841 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11078, d107841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11078, d107841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11079 q = 1) (hb : d107842 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11079, d107842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11079, d107842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11080 q = 1) (hb : d107843 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11080, d107843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11080, d107843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11081 q = 1) (hb : d107844 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11081, d107844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11081, d107844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11082 q = 1) (hb : d107845 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11082, d107845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11082, d107845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15948 (p : Pattern) (ha : d10900 p = 1) (hb : d107709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d107675 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15934 q ha hb
    | true =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d107676 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d107679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15935 q ha hb
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d107680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d107681 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d107682 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d107682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d107682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10899 q = 1) (hb : d107708 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10899, d107708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10899, d107708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10900 q = 1) (hb : d107709 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10900, d107709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10900, d107709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15949 (p : Pattern) (ha : d10902 p = 1) (hb : d107711 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d107679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15935 q ha hb
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d107680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d107685 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10877 q = 1) (hb : d107686 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d107686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10877, d107686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10901 q = 1) (hb : d107710 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10901, d107710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10901, d107710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10902 q = 1) (hb : d107711 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10902, d107711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10902, d107711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15950 (p : Pattern) (ha : d10909 p = 1) (hb : d107718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d107675 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15934 q ha hb
    | true =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d107676 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d107679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15935 q ha hb
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d107680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d107681 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10907 q = 1) (hb : d107716 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10907, d107716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10907, d107716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10908 q = 1) (hb : d107717 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10908, d107717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10908, d107717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10909 q = 1) (hb : d107718 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10909, d107718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10909, d107718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15951 (p : Pattern) (ha : d10912 p = 1) (hb : d107721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d107679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15935 q ha hb
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d107680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d107685 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10910 q = 1) (hb : d107719 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10910, d107719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10910, d107719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10911 q = 1) (hb : d107720 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10911, d107720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10911, d107720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10912 q = 1) (hb : d107721 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10912, d107721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10912, d107721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15952 (p : Pattern) (ha : d10921 p = 1) (hb : d107730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10916 q = 1) (hb : d107725 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10916, d107725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro77 q ha hb
    | true =>
      simp only [d10916, d107725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10917 q = 1) (hb : d107726 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10917, d107726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10917, d107726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10918 q = 1) (hb : d107727 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10918, d107727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10918, d107727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10742 q = 1) (hb : d107579 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10742, d107579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro43 q ha hb
    | true =>
      simp only [d10742, d107579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10743 q = 1) (hb : d107580 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10743, d107580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10743, d107580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10744 q = 1) (hb : d107581 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10744, d107581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10744, d107581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10919 q = 1) (hb : d107728 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10919, d107728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10919, d107728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10649 q = 1) (hb : d107486 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro20 q ha hb
    | true =>
      simp only [d10649, d107486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10650 q = 1) (hb : d107487 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10650, d107487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10651 q = 1) (hb : d107488 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10651, d107488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10745 q = 1) (hb : d107582 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10745, d107582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10745, d107582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10920 q = 1) (hb : d107729 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d10920, d107729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10920, d107729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d10921 q = 1) (hb : d107730 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d10921, d107730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d10921, d107730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro15953 (p : Pattern) (ha : d10927 p = 1) (hb : d107736 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10922 q = 1) (hb : d107731 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10922, d107731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15952 q ha hb
    | true =>
      simp only [d10922, d107731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10923 q = 1) (hb : d107732 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10923, d107732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10923, d107732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10866 q = 1) (hb : d107675 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15934 q ha hb
    | true =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10867 q = 1) (hb : d107676 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10924 q = 1) (hb : d107733 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10924, d107733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10924, d107733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10925 q = 1) (hb : d107734 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10925, d107734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10925, d107734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10926 q = 1) (hb : d107735 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10926, d107735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10926, d107735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10927 q = 1) (hb : d107736 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10927, d107736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10927, d107736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15954 (p : Pattern) (ha : d10955 p = 1) (hb : d107742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d107675 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15934 q ha hb
    | true =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d107676 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10952 q = 1) (hb : d107739 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10952, d107739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10952, d107739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10953 q = 1) (hb : d107740 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10953, d107740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10953, d107740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10954 q = 1) (hb : d107741 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10954, d107741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10954, d107741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10955 q = 1) (hb : d107742 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10955, d107742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10955, d107742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15955 (p : Pattern) (ha : d107748 p = 1) (hb : d108861 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10903 q = 1) (hb : d107712 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10903, d107712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15948 q ha hb
    | true =>
      simp only [d10903, d107712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15949 q ha hb
  have h2 (q : Pattern) (ha : d10904 q = 1) (hb : d107713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10904, d107713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10904, d107713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10905 q = 1) (hb : d107714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10905, d107714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10905, d107714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10906 q = 1) (hb : d107715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10906, d107715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10906, d107715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10913 q = 1) (hb : d107722 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10913, d107722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15950 q ha hb
    | true =>
      simp only [d10913, d107722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15951 q ha hb
  have h6 (q : Pattern) (ha : d10914 q = 1) (hb : d107723 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10914, d107723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10914, d107723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10915 q = 1) (hb : d107724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10915, d107724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10915, d107724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10928 q = 1) (hb : d107737 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10928, d107737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15953 q ha hb
    | true =>
      simp only [d10928, d107737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15936 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107689 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107738 q = 1) (hb : d108857 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107738, d108857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d107738, d108857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10956 q = 1) (hb : d107743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10956, d107743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15954 q ha hb
    | true =>
      simp only [d10956, d107743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10957 q = 1) (hb : d107744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10957, d107744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10957, d107744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d107745 q = 1) (hb : d108858 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107745, d108858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107745, d108858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d107746 q = 1) (hb : d108859 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107746, d108859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107746, d108859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107747 q = 1) (hb : d108860 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107747, d108860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107747, d108860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107748 q = 1) (hb : d108861 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107748, d108861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107748, d108861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro15956 (p : Pattern) (ha : d10962 p = 1) (hb : d107749 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d107675 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15934 q ha hb
    | true =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d107676 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d107679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15935 q ha hb
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d107680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d107681 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10873 q = 1) (hb : d107682 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10873, d107682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10873, d107682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10899 q = 1) (hb : d107708 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10899, d107708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10899, d107708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10962 q = 1) (hb : d107749 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10962, d107749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10962, d107749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15957 (p : Pattern) (ha : d10963 p = 1) (hb : d107750 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d107679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15935 q ha hb
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d107680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d107685 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10877 q = 1) (hb : d107686 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10877, d107686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10877, d107686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10901 q = 1) (hb : d107710 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10901, d107710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10901, d107710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10963 q = 1) (hb : d107750 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10963, d107750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10963, d107750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15958 (p : Pattern) (ha : d10968 p = 1) (hb : d107755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d107675 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15934 q ha hb
    | true =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d107676 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10870 q = 1) (hb : d107679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15935 q ha hb
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10871 q = 1) (hb : d107680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10872 q = 1) (hb : d107681 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10872, d107681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10907 q = 1) (hb : d107716 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10907, d107716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10907, d107716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10908 q = 1) (hb : d107717 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10908, d107717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10908, d107717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10968 q = 1) (hb : d107755 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10968, d107755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10968, d107755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15959 (p : Pattern) (ha : d10969 p = 1) (hb : d107756 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10870 q = 1) (hb : d107679 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15935 q ha hb
    | true =>
      simp only [d10870, d107679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10871 q = 1) (hb : d107680 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10871, d107680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10876 q = 1) (hb : d107685 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10876, d107685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10910 q = 1) (hb : d107719 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10910, d107719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10910, d107719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10911 q = 1) (hb : d107720 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10911, d107720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10911, d107720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10969 q = 1) (hb : d107756 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10969, d107756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10969, d107756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15960 (p : Pattern) (ha : d10973 p = 1) (hb : d107760 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10922 q = 1) (hb : d107731 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10922, d107731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15952 q ha hb
    | true =>
      simp only [d10922, d107731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10923 q = 1) (hb : d107732 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10923, d107732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10923, d107732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10866 q = 1) (hb : d107675 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15934 q ha hb
    | true =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10867 q = 1) (hb : d107676 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10924 q = 1) (hb : d107733 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10924, d107733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10924, d107733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10925 q = 1) (hb : d107734 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10925, d107734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10925, d107734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10926 q = 1) (hb : d107735 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10926, d107735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10926, d107735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10973 q = 1) (hb : d107760 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10973, d107760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10973, d107760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15961 (p : Pattern) (ha : d10979 p = 1) (hb : d107763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10866 q = 1) (hb : d107675 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15934 q ha hb
    | true =>
      simp only [d10866, d107675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10867 q = 1) (hb : d107676 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10867, d107676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10952 q = 1) (hb : d107739 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d10952, d107739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10952, d107739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10953 q = 1) (hb : d107740 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d10953, d107740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10953, d107740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10954 q = 1) (hb : d107741 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d10954, d107741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10954, d107741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10979 q = 1) (hb : d107763 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d10979, d107763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10979, d107763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15962 (p : Pattern) (ha : d107769 p = 1) (hb : d108866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10903 q = 1) (hb : d107712 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10903, d107712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15948 q ha hb
    | true =>
      simp only [d10903, d107712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15949 q ha hb
  have h2 (q : Pattern) (ha : d10904 q = 1) (hb : d107713 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10904, d107713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10904, d107713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10905 q = 1) (hb : d107714 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10905, d107714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10905, d107714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10906 q = 1) (hb : d107715 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10906, d107715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10906, d107715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10913 q = 1) (hb : d107722 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10913, d107722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15950 q ha hb
    | true =>
      simp only [d10913, d107722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15951 q ha hb
  have h6 (q : Pattern) (ha : d10914 q = 1) (hb : d107723 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10914, d107723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10914, d107723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10915 q = 1) (hb : d107724 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10915, d107724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10915, d107724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10928 q = 1) (hb : d107737 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10928, d107737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15953 q ha hb
    | true =>
      simp only [d10928, d107737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15936 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107689 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107738 q = 1) (hb : d108857 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107738, d108857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d107738, d108857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d10956 q = 1) (hb : d107743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10956, d107743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15954 q ha hb
    | true =>
      simp only [d10956, d107743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d10957 q = 1) (hb : d107744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10957, d107744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d10957, d107744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d107745 q = 1) (hb : d108858 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107745, d108858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107745, d108858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d107746 q = 1) (hb : d108859 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107746, d108859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107746, d108859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107747 q = 1) (hb : d108860 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107747, d108860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107747, d108860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d10964 q = 1) (hb : d107751 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10964, d107751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15956 q ha hb
    | true =>
      simp only [d10964, d107751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15957 q ha hb
  have h17 (q : Pattern) (ha : d10965 q = 1) (hb : d107752 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10965, d107752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10965, d107752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d10966 q = 1) (hb : d107753 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10966, d107753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d10966, d107753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h19 (q : Pattern) (ha : d10967 q = 1) (hb : d107754 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10967, d107754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10967, d107754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d10970 q = 1) (hb : d107757 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10970, d107757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15958 q ha hb
    | true =>
      simp only [d10970, d107757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15959 q ha hb
  have h21 (q : Pattern) (ha : d10971 q = 1) (hb : d107758 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10971, d107758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10971, d107758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d10972 q = 1) (hb : d107759 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10972, d107759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d10972, d107759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h23 (q : Pattern) (ha : d10974 q = 1) (hb : d107761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10974, d107761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15960 q ha hb
    | true =>
      simp only [d10974, d107761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15939 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d107699 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d107762 q = 1) (hb : d108862 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107762, d108862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q hb ha
    | true =>
      simp only [d107762, d108862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d10980 q = 1) (hb : d107764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10980, d107764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15961 q ha hb
    | true =>
      simp only [d10980, d107764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h27 (q : Pattern) (ha : d10981 q = 1) (hb : d107765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10981, d107765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d10981, d107765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h28 (q : Pattern) (ha : d107766 q = 1) (hb : d108863 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107766, d108863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d107766, d108863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q hb ha
  have h29 (q : Pattern) (ha : d107767 q = 1) (hb : d108864 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107767, d108864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q hb ha
    | true =>
      simp only [d107767, d108864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d107768 q = 1) (hb : d108865 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107768, d108865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q hb ha
    | true =>
      simp only [d107768, d108865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d107769 q = 1) (hb : d108866 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107769, d108866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d107769, d108866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro15963 (p : Pattern) (ha : d107789 p = 1) (hb : d108873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10974 q = 1) (hb : d107761 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10974, d107761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15960 q ha hb
    | true =>
      simp only [d10974, d107761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15939 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107699 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107762 q = 1) (hb : d108862 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107762, d108862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107762, d108862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d10980 q = 1) (hb : d107764 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10980, d107764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15961 q ha hb
    | true =>
      simp only [d10980, d107764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10981 q = 1) (hb : d107765 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10981, d107765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10981, d107765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d107766 q = 1) (hb : d108863 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107766, d108863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107766, d108863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107787 q = 1) (hb : d108871 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107787, d108871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107787, d108871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107788 q = 1) (hb : d108872 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107788, d108872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107788, d108872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107789 q = 1) (hb : d108873 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107789, d108873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107789, d108873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro15964 (p : Pattern) (ha : d11018 p = 1) (hb : d107802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11013 q = 1) (hb : d107797 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11013, d107797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro81 q ha hb
    | true =>
      simp only [d11013, d107797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11014 q = 1) (hb : d107798 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11014, d107798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11014, d107798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11015 q = 1) (hb : d107799 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11015, d107799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11015, d107799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10814 q = 1) (hb : d107636 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d107636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d10814, d107636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10815 q = 1) (hb : d107637 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d107637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10815, d107637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10816 q = 1) (hb : d107638 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d107638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10816, d107638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11016 q = 1) (hb : d107800 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11016, d107800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11016, d107800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d10686 q = 1) (hb : d107523 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d10687 q = 1) (hb : d107524 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d10688 q = 1) (hb : d107525 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10817 q = 1) (hb : d107639 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d107639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10817, d107639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11017 q = 1) (hb : d107801 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11017, d107801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11017, d107801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11018 q = 1) (hb : d107802 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11018, d107802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d11018, d107802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro15965 (p : Pattern) (ha : d11023 p = 1) (hb : d107807 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10814 q = 1) (hb : d107636 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10814, d107636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro47 q ha hb
    | true =>
      simp only [d10814, d107636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10815 q = 1) (hb : d107637 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10815, d107637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10815, d107637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10816 q = 1) (hb : d107638 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10816, d107638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10816, d107638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10686 q = 1) (hb : d107523 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro24 q ha hb
    | true =>
      simp only [d10686, d107523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10687 q = 1) (hb : d107524 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10687, d107524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10688 q = 1) (hb : d107525 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10688, d107525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10817 q = 1) (hb : d107639 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d10817, d107639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10817, d107639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11021 q = 1) (hb : d107805 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11021, d107805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11021, d107805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11022 q = 1) (hb : d107806 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11022, d107806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11022, d107806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11023 q = 1) (hb : d107807 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11023, d107807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11023, d107807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro15966 (p : Pattern) (ha : d11029 p = 1) (hb : d107813 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11019 q = 1) (hb : d107803 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11019, d107803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15964 q ha hb
    | true =>
      simp only [d11019, d107803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11020 q = 1) (hb : d107804 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11020, d107804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11020, d107804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11024 q = 1) (hb : d107808 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d107808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15965 q ha hb
    | true =>
      simp only [d11024, d107808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11025 q = 1) (hb : d107809 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d107809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d107809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11026 q = 1) (hb : d107810 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11026, d107810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11026, d107810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11027 q = 1) (hb : d107811 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11027, d107811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11027, d107811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11028 q = 1) (hb : d107812 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11028, d107812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11028, d107812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11029 q = 1) (hb : d107813 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11029, d107813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11029, d107813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15967 (p : Pattern) (ha : d11037 p = 1) (hb : d107821 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11024 q = 1) (hb : d107808 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d107808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15965 q ha hb
    | true =>
      simp only [d11024, d107808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11025 q = 1) (hb : d107809 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d107809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d107809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11032 q = 1) (hb : d107816 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11032, d107816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15945 q ha hb
    | true =>
      simp only [d11032, d107816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11033 q = 1) (hb : d107817 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11033, d107817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11033, d107817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11034 q = 1) (hb : d107818 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11034, d107818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11034, d107818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11035 q = 1) (hb : d107819 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11035, d107819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11035, d107819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11036 q = 1) (hb : d107820 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11036, d107820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11036, d107820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11037 q = 1) (hb : d107821 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11037, d107821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11037, d107821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15968 (p : Pattern) (ha : d11065 p = 1) (hb : d107832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11024 q = 1) (hb : d107808 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11024, d107808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15965 q ha hb
    | true =>
      simp only [d11024, d107808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11025 q = 1) (hb : d107809 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11025, d107809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11025, d107809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11062 q = 1) (hb : d107829 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11062, d107829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11062, d107829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11063 q = 1) (hb : d107830 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11063, d107830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11063, d107830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11064 q = 1) (hb : d107831 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11064, d107831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11064, d107831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11065 q = 1) (hb : d107832 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11065, d107832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11065, d107832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15969 (p : Pattern) (ha : d107838 p = 1) (hb : d108883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11038 q = 1) (hb : d107822 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11038, d107822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15966 q ha hb
    | true =>
      simp only [d11038, d107822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15967 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d107827 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d107828 q = 1) (hb : d108879 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107828, d108879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d107828, d108879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d11066 q = 1) (hb : d107833 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11066, d107833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15968 q ha hb
    | true =>
      simp only [d11066, d107833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11067 q = 1) (hb : d107834 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11067, d107834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11067, d107834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d107835 q = 1) (hb : d108880 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107835, d108880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d107835, d108880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d107836 q = 1) (hb : d108881 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107836, d108881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107836, d108881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d107837 q = 1) (hb : d108882 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107837, d108882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107837, d108882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d107838 q = 1) (hb : d108883 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107838, d108883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107838, d108883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro15970 (p : Pattern) (ha : d107851 p = 1) (hb : d108889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10886 q = 1) (hb : d107695 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10886, d107695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10886, d107695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15938 q ha hb
  have h2 (q : Pattern) (ha : d10887 q = 1) (hb : d107696 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10887, d107696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10887, d107696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d10896 q = 1) (hb : d107705 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10896, d107705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15938 q ha hb
    | true =>
      simp only [d10896, d107705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15941 q ha hb
  have h4 (q : Pattern) (ha : d10897 q = 1) (hb : d107706 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10897, d107706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10897, d107706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10898 q = 1) (hb : d107707 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d10898, d107707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10898, d107707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107770 q = 1) (hb : d108867 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107770, d108867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15955 q ha hb
    | true =>
      simp only [d107770, d108867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15962 q ha hb
  have h7 (q : Pattern) (ha : d10999 q = 1) (hb : d107783 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10999, d107783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15942 q ha hb
    | true =>
      simp only [d10999, d107783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15943 q ha hb
  have h8 (q : Pattern) (ha : d107784 q = 1) (hb : d108868 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107784, d108868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d107784, d108868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d107785 q = 1) (hb : d108869 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107785, d108869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d107785, d108869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d107786 q = 1) (hb : d108870 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107786, d108870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d107786, d108870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d107790 q = 1) (hb : d108874 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107790, d108874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107790, d108874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15963 q ha hb
  have h12 (q : Pattern) (ha : d11008 q = 1) (hb : d107792 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11008, d107792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11008, d107792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15944 q ha hb
  have h13 (q : Pattern) (ha : d107793 q = 1) (hb : d108875 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107793, d108875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d107793, d108875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d107794 q = 1) (hb : d108876 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107794, d108876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d107794, d108876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d107795 q = 1) (hb : d108877 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107795, d108877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d107795, d108877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d107796 q = 1) (hb : d108878 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107796, d108878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107796, d108878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d107839 q = 1) (hb : d108884 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d107839, d108884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107839, d108884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15969 q ha hb
  have h18 (q : Pattern) (ha : d11083 q = 1) (hb : d107846 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11083, d107846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11083, d107846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15947 q ha hb
  have h19 (q : Pattern) (ha : d107847 q = 1) (hb : d108885 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d107847, d108885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d107847, d108885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d107848 q = 1) (hb : d108886 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d107848, d108886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d107848, d108886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d107849 q = 1) (hb : d108887 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d107849, d108887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d107849, d108887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d107850 q = 1) (hb : d108888 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d107850, d108888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d107850, d108888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d107851 q = 1) (hb : d108889 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d107851, d108889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d107851, d108889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro15971 (p : Pattern) (ha : d107857 p = 1) (hb : d108895 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d107852 q = 1) (hb : d108890 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d107852, d108890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107852, d108890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15970 q ha hb
  have h2 (q : Pattern) (ha : d107853 q = 1) (hb : d108891 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d107853, d108891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107853, d108891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d107854 q = 1) (hb : d108892 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d107854, d108892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107854, d108892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d107855 q = 1) (hb : d108893 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d107855, d108893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107855, d108893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d107856 q = 1) (hb : d108894 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d107856, d108894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107856, d108894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d107857 q = 1) (hb : d108895 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d107857, d108895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107857, d108895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15972 (p : Pattern) (ha : d11105 p = 1) (hb : d107868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11096 q = 1) (hb : d107859 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d107859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
    | true =>
      simp only [d11096, d107859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11097 q = 1) (hb : d107860 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d107860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11097, d107860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11098 q = 1) (hb : d107861 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d107861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11098, d107861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11099 q = 1) (hb : d107862 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d107862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d11099, d107862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11100 q = 1) (hb : d107863 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d107863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d107863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11101 q = 1) (hb : d107864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d107864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d107864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11102 q = 1) (hb : d107865 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d107865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11102, d107865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11103 q = 1) (hb : d107866 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11103, d107866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11103, d107866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11104 q = 1) (hb : d107867 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11104, d107867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11104, d107867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11105 q = 1) (hb : d107868 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11105, d107868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d11105, d107868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h10 p ha hb
theorem andIntro15973 (p : Pattern) (ha : d11109 p = 1) (hb : d107872 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11099 q = 1) (hb : d107862 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d107862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d11099, d107862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11100 q = 1) (hb : d107863 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d107863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d107863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11101 q = 1) (hb : d107864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d107864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d107864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11103 q = 1) (hb : d107866 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11103, d107866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11103, d107866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11108 q = 1) (hb : d107871 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11108, d107871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11108, d107871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11109 q = 1) (hb : d107872 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11109, d107872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11109, d107872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15974 (p : Pattern) (ha : d11115 p = 1) (hb : d107878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d107869 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15972 q ha hb
    | true =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d107870 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d107873 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15973 q ha hb
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d107874 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d107875 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d107876 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d107876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d107876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11114 q = 1) (hb : d107877 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11114, d107877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11114, d107877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11115 q = 1) (hb : d107878 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11115, d107878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11115, d107878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15975 (p : Pattern) (ha : d11119 p = 1) (hb : d107882 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d107873 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15973 q ha hb
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d107874 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d107879 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11117 q = 1) (hb : d107880 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d107880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11117, d107880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11118 q = 1) (hb : d107881 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11118, d107881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11118, d107881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11119 q = 1) (hb : d107882 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11119, d107882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11119, d107882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15976 (p : Pattern) (ha : d11125 p = 1) (hb : d107888 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11120 q = 1) (hb : d107883 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d107883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15974 q ha hb
    | true =>
      simp only [d11120, d107883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15975 q ha hb
  have h2 (q : Pattern) (ha : d11121 q = 1) (hb : d107884 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d107884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d107884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11122 q = 1) (hb : d107885 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d107885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11122, d107885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11123 q = 1) (hb : d107886 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d107886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d107886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11124 q = 1) (hb : d107887 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d107887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d107887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11125 q = 1) (hb : d107888 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11125, d107888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11125, d107888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15977 (p : Pattern) (ha : d11128 p = 1) (hb : d107891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d107869 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15972 q ha hb
    | true =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d107870 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d107873 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15973 q ha hb
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d107874 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d107875 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d107876 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d107876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d107876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11114 q = 1) (hb : d107877 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11114, d107877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11114, d107877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11128 q = 1) (hb : d107891 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11128, d107891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11128, d107891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15978 (p : Pattern) (ha : d11129 p = 1) (hb : d107892 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d107873 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15973 q ha hb
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d107874 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d107879 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11117 q = 1) (hb : d107880 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d107880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11117, d107880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11118 q = 1) (hb : d107881 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11118, d107881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11118, d107881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11129 q = 1) (hb : d107892 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11129, d107892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11129, d107892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15979 (p : Pattern) (ha : d11135 p = 1) (hb : d107898 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11120 q = 1) (hb : d107883 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d107883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15974 q ha hb
    | true =>
      simp only [d11120, d107883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15975 q ha hb
  have h2 (q : Pattern) (ha : d11121 q = 1) (hb : d107884 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d107884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d107884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11122 q = 1) (hb : d107885 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d107885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11122, d107885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11123 q = 1) (hb : d107886 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d107886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d107886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11124 q = 1) (hb : d107887 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d107887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d107887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11130 q = 1) (hb : d107893 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11130, d107893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15977 q ha hb
    | true =>
      simp only [d11130, d107893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15978 q ha hb
  have h7 (q : Pattern) (ha : d11131 q = 1) (hb : d107894 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11131, d107894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11131, d107894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11132 q = 1) (hb : d107895 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11132, d107895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11132, d107895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11133 q = 1) (hb : d107896 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11133, d107896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11133, d107896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11134 q = 1) (hb : d107897 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11134, d107897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11134, d107897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11135 q = 1) (hb : d107898 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11135, d107898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11135, d107898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15980 (p : Pattern) (ha : d11243 p = 1) (hb : d107978 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11120 q = 1) (hb : d107883 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11120, d107883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15974 q ha hb
    | true =>
      simp only [d11120, d107883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15975 q ha hb
  have h2 (q : Pattern) (ha : d11121 q = 1) (hb : d107884 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11121, d107884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11121, d107884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11122 q = 1) (hb : d107885 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11122, d107885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11122, d107885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11123 q = 1) (hb : d107886 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11123, d107886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11123, d107886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11124 q = 1) (hb : d107887 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11124, d107887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11124, d107887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11238 q = 1) (hb : d107973 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11238, d107973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15975 q ha hb
    | true =>
      simp only [d11238, d107973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11239 q = 1) (hb : d107974 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11239, d107974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11239, d107974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11240 q = 1) (hb : d107975 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11240, d107975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11240, d107975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11241 q = 1) (hb : d107976 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11241, d107976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11241, d107976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11242 q = 1) (hb : d107977 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11242, d107977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11242, d107977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11243 q = 1) (hb : d107978 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11243, d107978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11243, d107978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15981 (p : Pattern) (ha : d11249 p = 1) (hb : d107984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11238 q = 1) (hb : d107973 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11238, d107973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15975 q ha hb
    | true =>
      simp only [d11238, d107973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11239 q = 1) (hb : d107974 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11239, d107974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11239, d107974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11240 q = 1) (hb : d107975 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11240, d107975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11240, d107975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11241 q = 1) (hb : d107976 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11241, d107976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11241, d107976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11242 q = 1) (hb : d107977 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11242, d107977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11242, d107977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11244 q = 1) (hb : d107979 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11244, d107979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15978 q ha hb
    | true =>
      simp only [d11244, d107979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11245 q = 1) (hb : d107980 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11245, d107980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11245, d107980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11246 q = 1) (hb : d107981 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11246, d107981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11246, d107981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11247 q = 1) (hb : d107982 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11247, d107982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11247, d107982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11248 q = 1) (hb : d107983 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11248, d107983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11248, d107983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11249 q = 1) (hb : d107984 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11249, d107984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11249, d107984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro15982 (p : Pattern) (ha : d11258 p = 1) (hb : d107993 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11244 q = 1) (hb : d107979 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11244, d107979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15978 q ha hb
    | true =>
      simp only [d11244, d107979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11245 q = 1) (hb : d107980 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11245, d107980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11245, d107980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11246 q = 1) (hb : d107981 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11246, d107981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11246, d107981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11247 q = 1) (hb : d107982 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11247, d107982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11247, d107982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11248 q = 1) (hb : d107983 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11248, d107983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11248, d107983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11258 q = 1) (hb : d107993 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11258, d107993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11258, d107993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15983 (p : Pattern) (ha : d11289 p = 1) (hb : d108024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11271 q = 1) (hb : d108006 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11271, d108006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro115 q ha hb
    | true =>
      simp only [d11271, d108006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11272 q = 1) (hb : d108007 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11272, d108007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11272, d108007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11273 q = 1) (hb : d108008 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11273, d108008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11273, d108008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11279 q = 1) (hb : d108014 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11279, d108014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11279, d108014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11288 q = 1) (hb : d108023 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11288, d108023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11288, d108023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11289 q = 1) (hb : d108024 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11289, d108024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11289, d108024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15984 (p : Pattern) (ha : d11345 p = 1) (hb : d108035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11290 q = 1) (hb : d108025 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11290, d108025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15983 q ha hb
    | true =>
      simp only [d11290, d108025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11291 q = 1) (hb : d108026 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11291, d108026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11291, d108026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11342 q = 1) (hb : d108032 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11342, d108032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11342, d108032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11343 q = 1) (hb : d108033 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11343, d108033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11343, d108033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11344 q = 1) (hb : d108034 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11344, d108034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11344, d108034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11345 q = 1) (hb : d108035 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11345, d108035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11345, d108035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15985 (p : Pattern) (ha : d11351 p = 1) (hb : d108062 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11346 q = 1) (hb : d108057 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11346, d108057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15984 q ha hb
    | true =>
      simp only [d11346, d108057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11347 q = 1) (hb : d108058 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11347, d108058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11347, d108058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11348 q = 1) (hb : d108059 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11348, d108059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11348, d108059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11349 q = 1) (hb : d108060 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11349, d108060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11349, d108060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11350 q = 1) (hb : d108061 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11350, d108061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11350, d108061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11351 q = 1) (hb : d108062 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d11351, d108062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11351, d108062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15986 (p : Pattern) (ha : d11140 p = 1) (hb : d107903 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d107869 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15972 q ha hb
    | true =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d107870 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d107873 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15973 q ha hb
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d107874 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d107875 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d107876 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d107876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d107876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11139 q = 1) (hb : d107902 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11139, d107902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11139, d107902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11140 q = 1) (hb : d107903 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11140, d107903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11140, d107903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15987 (p : Pattern) (ha : d11142 p = 1) (hb : d107905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d107873 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15973 q ha hb
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d107874 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d107879 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11117 q = 1) (hb : d107880 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d107880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11117, d107880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11141 q = 1) (hb : d107904 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11141, d107904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11141, d107904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11142 q = 1) (hb : d107905 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11142, d107905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11142, d107905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15988 (p : Pattern) (ha : d11149 p = 1) (hb : d107912 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d107869 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15972 q ha hb
    | true =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d107870 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d107873 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15973 q ha hb
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d107874 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d107875 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11147 q = 1) (hb : d107910 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11147, d107910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11147, d107910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11148 q = 1) (hb : d107911 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11148, d107911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11148, d107911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11149 q = 1) (hb : d107912 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11149, d107912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11149, d107912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15989 (p : Pattern) (ha : d11152 p = 1) (hb : d107915 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d107873 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15973 q ha hb
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d107874 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d107879 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11150 q = 1) (hb : d107913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11150, d107913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11150, d107913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11151 q = 1) (hb : d107914 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11151, d107914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11151, d107914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11152 q = 1) (hb : d107915 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11152, d107915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11152, d107915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15990 (p : Pattern) (ha : d11161 p = 1) (hb : d107924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11156 q = 1) (hb : d107919 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11156, d107919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro123 q ha hb
    | true =>
      simp only [d11156, d107919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11157 q = 1) (hb : d107920 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11157, d107920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11157, d107920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11158 q = 1) (hb : d107921 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11158, d107921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11158, d107921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11096 q = 1) (hb : d107859 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d107859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
    | true =>
      simp only [d11096, d107859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11097 q = 1) (hb : d107860 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d107860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11097, d107860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11098 q = 1) (hb : d107861 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d107861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11098, d107861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11159 q = 1) (hb : d107922 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11159, d107922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11159, d107922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11099 q = 1) (hb : d107862 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d107862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d11099, d107862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11100 q = 1) (hb : d107863 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d107863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d107863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11101 q = 1) (hb : d107864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d107864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d107864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11102 q = 1) (hb : d107865 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d107865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11102, d107865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d11160 q = 1) (hb : d107923 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11160, d107923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11160, d107923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11161 q = 1) (hb : d107924 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11161, d107924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d11161, d107924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro15991 (p : Pattern) (ha : d11167 p = 1) (hb : d107930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11162 q = 1) (hb : d107925 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11162, d107925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15990 q ha hb
    | true =>
      simp only [d11162, d107925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11163 q = 1) (hb : d107926 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11163, d107926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11163, d107926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11106 q = 1) (hb : d107869 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15972 q ha hb
    | true =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11107 q = 1) (hb : d107870 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11164 q = 1) (hb : d107927 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11164, d107927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11164, d107927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11165 q = 1) (hb : d107928 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11165, d107928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11165, d107928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11166 q = 1) (hb : d107929 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11166, d107929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11166, d107929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11167 q = 1) (hb : d107930 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11167, d107930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11167, d107930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro15992 (p : Pattern) (ha : d11200 p = 1) (hb : d107938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11096 q = 1) (hb : d107859 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11096, d107859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro101 q ha hb
    | true =>
      simp only [d11096, d107859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11097 q = 1) (hb : d107860 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11097, d107860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11097, d107860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11098 q = 1) (hb : d107861 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11098, d107861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11098, d107861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d11099 q = 1) (hb : d107862 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11099, d107862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro102 q ha hb
    | true =>
      simp only [d11099, d107862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11100 q = 1) (hb : d107863 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11100, d107863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11100, d107863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11101 q = 1) (hb : d107864 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11101, d107864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11101, d107864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11102 q = 1) (hb : d107865 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11102, d107865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11102, d107865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11195 q = 1) (hb : d107933 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d11195, d107933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro9260 q ha hb
    | true =>
      simp only [d11195, d107933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d11196 q = 1) (hb : d107934 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d11196, d107934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11196, d107934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d11197 q = 1) (hb : d107935 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d11197, d107935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11197, d107935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d11198 q = 1) (hb : d107936 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d11198, d107936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d11198, d107936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d11199 q = 1) (hb : d107937 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d11199, d107937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11199, d107937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d11200 q = 1) (hb : d107938 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d11200, d107938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d11200, d107938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro15993 (p : Pattern) (ha : d11206 p = 1) (hb : d107944 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11201 q = 1) (hb : d107939 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11201, d107939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15992 q ha hb
    | true =>
      simp only [d11201, d107939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11202 q = 1) (hb : d107940 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11202, d107940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11202, d107940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11203 q = 1) (hb : d107941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11203, d107941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11203, d107941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11204 q = 1) (hb : d107942 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11204, d107942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11204, d107942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11205 q = 1) (hb : d107943 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11205, d107943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11205, d107943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11206 q = 1) (hb : d107944 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11206, d107944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11206, d107944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro15994 (p : Pattern) (ha : d107950 p = 1) (hb : d108901 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11143 q = 1) (hb : d107906 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11143, d107906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15986 q ha hb
    | true =>
      simp only [d11143, d107906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15987 q ha hb
  have h2 (q : Pattern) (ha : d11144 q = 1) (hb : d107907 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11144, d107907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11144, d107907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11145 q = 1) (hb : d107908 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11145, d107908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11145, d107908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11146 q = 1) (hb : d107909 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11146, d107909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11146, d107909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11153 q = 1) (hb : d107916 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11153, d107916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15988 q ha hb
    | true =>
      simp only [d11153, d107916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15989 q ha hb
  have h6 (q : Pattern) (ha : d11154 q = 1) (hb : d107917 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11154, d107917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11154, d107917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11155 q = 1) (hb : d107918 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11155, d107918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11155, d107918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11168 q = 1) (hb : d107931 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11168, d107931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15991 q ha hb
    | true =>
      simp only [d11168, d107931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15974 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d107883 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d107932 q = 1) (hb : d108897 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d107932, d108897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d107932, d108897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d11207 q = 1) (hb : d107945 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11207, d107945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15993 q ha hb
    | true =>
      simp only [d11207, d107945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d11208 q = 1) (hb : d107946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11208, d107946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d11208, d107946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d107947 q = 1) (hb : d108898 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d107947, d108898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d107947, d108898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d107948 q = 1) (hb : d108899 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d107948, d108899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d107948, d108899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d107949 q = 1) (hb : d108900 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d107949, d108900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d107949, d108900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d107950 q = 1) (hb : d108901 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d107950, d108901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d107950, d108901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro15995 (p : Pattern) (ha : d11213 p = 1) (hb : d107951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d107869 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15972 q ha hb
    | true =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d107870 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d107873 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15973 q ha hb
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d107874 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d107875 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11113 q = 1) (hb : d107876 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11113, d107876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11113, d107876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11139 q = 1) (hb : d107902 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11139, d107902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11139, d107902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d11213 q = 1) (hb : d107951 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11213, d107951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11213, d107951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15996 (p : Pattern) (ha : d11214 p = 1) (hb : d107952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d107873 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15973 q ha hb
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d107874 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d107879 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11117 q = 1) (hb : d107880 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11117, d107880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d11117, d107880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d11141 q = 1) (hb : d107904 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11141, d107904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11141, d107904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11214 q = 1) (hb : d107952 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11214, d107952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11214, d107952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15997 (p : Pattern) (ha : d11219 p = 1) (hb : d107957 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11106 q = 1) (hb : d107869 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15972 q ha hb
    | true =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11107 q = 1) (hb : d107870 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11110 q = 1) (hb : d107873 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15973 q ha hb
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11111 q = 1) (hb : d107874 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11112 q = 1) (hb : d107875 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11112, d107875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11147 q = 1) (hb : d107910 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11147, d107910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11147, d107910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d11148 q = 1) (hb : d107911 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11148, d107911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11148, d107911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11219 q = 1) (hb : d107957 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11219, d107957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11219, d107957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro15998 (p : Pattern) (ha : d11220 p = 1) (hb : d107958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11110 q = 1) (hb : d107873 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15973 q ha hb
    | true =>
      simp only [d11110, d107873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11111 q = 1) (hb : d107874 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11111, d107874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11116 q = 1) (hb : d107879 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11116, d107879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11150 q = 1) (hb : d107913 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11150, d107913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11150, d107913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11151 q = 1) (hb : d107914 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11151, d107914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d11151, d107914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d11220 q = 1) (hb : d107958 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11220, d107958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11220, d107958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro15999 (p : Pattern) (ha : d11224 p = 1) (hb : d107962 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11162 q = 1) (hb : d107925 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11162, d107925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15990 q ha hb
    | true =>
      simp only [d11162, d107925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d11163 q = 1) (hb : d107926 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11163, d107926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11163, d107926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11106 q = 1) (hb : d107869 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro15972 q ha hb
    | true =>
      simp only [d11106, d107869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11107 q = 1) (hb : d107870 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11107, d107870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11164 q = 1) (hb : d107927 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d11164, d107927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11164, d107927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d11165 q = 1) (hb : d107928 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d11165, d107928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d11165, d107928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d11166 q = 1) (hb : d107929 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d11166, d107929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d11166, d107929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d11224 q = 1) (hb : d107962 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d11224, d107962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d11224, d107962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
end NetHack.Soko22Hazard87
