import NetHack.Soko22Hazard87.EqIntroBlocks0024
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro6250 (p : Pattern) (selected : d1877 p = 0) : d53203 p = 1 := by
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
  have h6 (q : Pattern) (selected : d1871 q = 0) : d53197 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1871, d53197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1871, d53197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1877 q = 0) : d53203 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1877, d53203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1877, d53203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro6251 (p : Pattern) (selected : d95824 p = 0) : d97121 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95817 q = 0) : d97114 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95817, d97114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6248 q selected
    | true =>
      simp only [d95817, d97114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6249 q selected
  have h2 (q : Pattern) (selected : d95818 q = 0) : d97115 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95818, d97115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95818, d97115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95819 q = 0) : d97116 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95819, d97116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95819, d97116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95820 q = 0) : d97117 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95820, d97117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6249 q selected
    | true =>
      simp only [d95820, d97117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6250 q selected
  have h5 (q : Pattern) (selected : d95821 q = 0) : d97118 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95821, d97118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95821, d97118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95822 q = 0) : d97119 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95822, d97119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95822, d97119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95823 q = 0) : d97120 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95823, d97120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95823, d97120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95824 q = 0) : d97121 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95824, d97121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95824, d97121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6252 (p : Pattern) (selected : d95828 p = 0) : d97125 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95820 q = 0) : d97117 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95820, d97117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6249 q selected
    | true =>
      simp only [d95820, d97117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6250 q selected
  have h2 (q : Pattern) (selected : d95821 q = 0) : d97118 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95821, d97118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95821, d97118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95822 q = 0) : d97119 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95822, d97119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95822, d97119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95827 q = 0) : d97124 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95827, d97124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95827, d97124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95828 q = 0) : d97125 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95828, d97125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95828, d97125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6253 (p : Pattern) (selected : d95834 p = 0) : d97131 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95825 q = 0) : d97122 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95825, d97122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6251 q selected
    | true =>
      simp only [d95825, d97122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95826 q = 0) : d97123 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95826, d97123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95826, d97123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95829 q = 0) : d97126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95829, d97126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6252 q selected
    | true =>
      simp only [d95829, d97126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95830 q = 0) : d97127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95830, d97127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95830, d97127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95831 q = 0) : d97128 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95831, d97128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95831, d97128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95832 q = 0) : d97129 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95832, d97129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95832, d97129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95833 q = 0) : d97130 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95833, d97130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95833, d97130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95834 q = 0) : d97131 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95834, d97131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95834, d97131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6254 (p : Pattern) (selected : d1887 p = 0) : d53213 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1883 q = 0) : d53209 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1883, d53209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1883, d53209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro473 q selected
  have h2 (q : Pattern) (selected : d1597 q = 0) : d53038 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1597, d53038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro473 q selected
    | true =>
      simp only [d1597, d53038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1884 q = 0) : d53210 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1884, d53210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1884, d53210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1598 q = 0) : d53039 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1598, d53039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1598, d53039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1885 q = 0) : d53211 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1885, d53211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1885, d53211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1886 q = 0) : d53212 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1886, d53212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1886, d53212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1887 q = 0) : d53213 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1887, d53213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1887, d53213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro6255 (p : Pattern) (selected : d95839 p = 0) : d97136 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95835 q = 0) : d97132 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95835, d97132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6250 q selected
    | true =>
      simp only [d95835, d97132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6254 q selected
  have h2 (q : Pattern) (selected : d95836 q = 0) : d97133 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95836, d97133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95836, d97133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95837 q = 0) : d97134 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95837, d97134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95837, d97134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95838 q = 0) : d97135 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95838, d97135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95838, d97135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95839 q = 0) : d97136 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95839, d97136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95839, d97136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6256 (p : Pattern) (selected : d95845 p = 0) : d97142 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95829 q = 0) : d97126 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95829, d97126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6252 q selected
    | true =>
      simp only [d95829, d97126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95830 q = 0) : d97127 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95830, d97127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95830, d97127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95840 q = 0) : d97137 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95840, d97137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6255 q selected
    | true =>
      simp only [d95840, d97137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95841 q = 0) : d97138 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95841, d97138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95841, d97138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95842 q = 0) : d97139 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95842, d97139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95842, d97139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95843 q = 0) : d97140 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95843, d97140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95843, d97140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95844 q = 0) : d97141 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95844, d97141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95844, d97141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95845 q = 0) : d97142 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95845, d97142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95845, d97142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6257 (p : Pattern) (selected : d1928 p = 0) : d53198 p = 1 := by
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
  have h6 (q : Pattern) (selected : d1922 q = 0) : d53191 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1922, d53191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1922, d53191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1924 q = 0) : d53194 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1924, d53194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1924, d53194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro503 q selected
  have h8 (q : Pattern) (selected : d1753 q = 0) : d53023 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro503 q selected
    | true =>
      simp only [d1753, d53023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1925 q = 0) : d53195 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1925, d53195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1925, d53195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1754 q = 0) : d53024 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1754, d53024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d1926 q = 0) : d53196 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1926, d53196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1926, d53196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1927 q = 0) : d53197 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1927, d53197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1927, d53197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d1928 q = 0) : d53198 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1928, d53198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1928, d53198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro6258 (p : Pattern) (selected : d1930 p = 0) : d53203 p = 1 := by
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
  have h6 (q : Pattern) (selected : d1927 q = 0) : d53197 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1927, d53197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1927, d53197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1930 q = 0) : d53203 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1930, d53203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1930, d53203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro6259 (p : Pattern) (selected : d1939 p = 0) : d53213 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1935 q = 0) : d53209 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1935, d53209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1935, d53209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro506 q selected
  have h2 (q : Pattern) (selected : d1768 q = 0) : d53038 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1768, d53038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro506 q selected
    | true =>
      simp only [d1768, d53038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1936 q = 0) : d53210 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1936, d53210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1936, d53210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1769 q = 0) : d53039 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1769, d53039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1769, d53039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1937 q = 0) : d53211 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1937, d53211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1937, d53211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1938 q = 0) : d53212 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1938, d53212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1938, d53212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1939 q = 0) : d53213 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1939, d53213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1939, d53213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro6260 (p : Pattern) (selected : d95854 p = 0) : d97145 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95847 q = 0) : d97117 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95847, d97117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6257 q selected
    | true =>
      simp only [d95847, d97117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6258 q selected
  have h2 (q : Pattern) (selected : d95848 q = 0) : d97118 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95848, d97118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95848, d97118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95849 q = 0) : d97119 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95849, d97119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95849, d97119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95850 q = 0) : d97132 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95850, d97132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6258 q selected
    | true =>
      simp only [d95850, d97132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6259 q selected
  have h5 (q : Pattern) (selected : d95851 q = 0) : d97133 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95851, d97133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95851, d97133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95852 q = 0) : d97134 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95852, d97134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95852, d97134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95853 q = 0) : d97144 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95853, d97144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95853, d97144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95854 q = 0) : d97145 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95854, d97145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95854, d97145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6261 (p : Pattern) (selected : d95858 p = 0) : d97136 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95850 q = 0) : d97132 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95850, d97132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6258 q selected
    | true =>
      simp only [d95850, d97132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6259 q selected
  have h2 (q : Pattern) (selected : d95851 q = 0) : d97133 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95851, d97133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95851, d97133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95852 q = 0) : d97134 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95852, d97134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95852, d97134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95857 q = 0) : d97135 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95857, d97135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95857, d97135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95858 q = 0) : d97136 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95858, d97136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95858, d97136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6262 (p : Pattern) (selected : d95864 p = 0) : d97151 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95855 q = 0) : d97146 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95855, d97146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6260 q selected
    | true =>
      simp only [d95855, d97146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95856 q = 0) : d97147 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95856, d97147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95856, d97147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95859 q = 0) : d97137 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95859, d97137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6261 q selected
    | true =>
      simp only [d95859, d97137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95860 q = 0) : d97138 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95860, d97138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95860, d97138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95861 q = 0) : d97148 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95861, d97148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95861, d97148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95862 q = 0) : d97149 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95862, d97149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95862, d97149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95863 q = 0) : d97150 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95863, d97150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95863, d97150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95864 q = 0) : d97151 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95864, d97151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95864, d97151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6263 (p : Pattern) (selected : d95868 p = 0) : d97155 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95859 q = 0) : d97137 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95859, d97137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6261 q selected
    | true =>
      simp only [d95859, d97137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95860 q = 0) : d97138 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95860, d97138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95860, d97138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95865 q = 0) : d97152 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95865, d97152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95865, d97152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95866 q = 0) : d97153 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95866, d97153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95866, d97153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95867 q = 0) : d97154 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95867, d97154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95867, d97154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d95868 q = 0) : d97155 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95868, d97155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95868, d97155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6264 (p : Pattern) (selected : d95872 p = 0) : d97145 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95820 q = 0) : d97117 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95820, d97117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6249 q selected
    | true =>
      simp only [d95820, d97117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6250 q selected
  have h2 (q : Pattern) (selected : d95821 q = 0) : d97118 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95821, d97118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95821, d97118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95822 q = 0) : d97119 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95822, d97119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95822, d97119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95835 q = 0) : d97132 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95835, d97132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6250 q selected
    | true =>
      simp only [d95835, d97132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6254 q selected
  have h5 (q : Pattern) (selected : d95836 q = 0) : d97133 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95836, d97133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95836, d97133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95837 q = 0) : d97134 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95837, d97134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95837, d97134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95871 q = 0) : d97144 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95871, d97144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95871, d97144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95872 q = 0) : d97145 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95872, d97145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95872, d97145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6265 (p : Pattern) (selected : d95878 p = 0) : d97161 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95873 q = 0) : d97146 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95873, d97146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6264 q selected
    | true =>
      simp only [d95873, d97146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95874 q = 0) : d97147 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95874, d97147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95874, d97147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95875 q = 0) : d97158 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95875, d97158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95875, d97158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95876 q = 0) : d97159 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95876, d97159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95876, d97159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95877 q = 0) : d97160 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95877, d97160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95877, d97160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d95878 q = 0) : d97161 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95878, d97161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95878, d97161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6266 (p : Pattern) (selected : d95884 p = 0) : d97167 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95846 q = 0) : d97143 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95846, d97143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6253 q selected
    | true =>
      simp only [d95846, d97143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6256 q selected
  have h2 (q : Pattern) (selected : d95869 q = 0) : d97156 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95869, d97156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6262 q selected
    | true =>
      simp only [d95869, d97156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6263 q selected
  have h3 (q : Pattern) (selected : d95870 q = 0) : d97157 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95870, d97157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95870, d97157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95879 q = 0) : d97162 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95879, d97162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6265 q selected
    | true =>
      simp only [d95879, d97162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95880 q = 0) : d97163 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95880, d97163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95880, d97163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d95881 q = 0) : d97164 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95881, d97164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95881, d97164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95882 q = 0) : d97165 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95882, d97165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95882, d97165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95883 q = 0) : d97166 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95883, d97166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95883, d97166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d95884 q = 0) : d97167 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d95884, d97167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95884, d97167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro6267 (p : Pattern) (selected : d95889 p = 0) : d97155 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95840 q = 0) : d97137 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95840, d97137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6255 q selected
    | true =>
      simp only [d95840, d97137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95841 q = 0) : d97138 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95841, d97138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95841, d97138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95886 q = 0) : d97152 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95886, d97152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95886, d97152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95887 q = 0) : d97153 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95887, d97153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95887, d97153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95888 q = 0) : d97154 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95888, d97154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95888, d97154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d95889 q = 0) : d97155 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95889, d97155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95889, d97155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6268 (p : Pattern) (selected : d95895 p = 0) : d97174 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95890 q = 0) : d97169 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95890, d97169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6267 q selected
    | true =>
      simp only [d95890, d97169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95891 q = 0) : d97170 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95891, d97170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95891, d97170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95892 q = 0) : d97171 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95892, d97171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95892, d97171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95893 q = 0) : d97172 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95893, d97172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95893, d97172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95894 q = 0) : d97173 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95894, d97173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95894, d97173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95895 q = 0) : d97174 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d95895, d97174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95895, d97174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6269 (p : Pattern) (selected : d95901 p = 0) : d97180 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95676 q = 0) : d96999 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95676, d96999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95676, d96999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6212 q selected
  have h2 (q : Pattern) (selected : d95677 q = 0) : d97000 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d95677, d97000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95677, d97000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d95686 q = 0) : d97009 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95686, d97009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6212 q selected
    | true =>
      simp only [d95686, d97009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6215 q selected
  have h4 (q : Pattern) (selected : d95687 q = 0) : d97010 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d95687, d97010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95687, d97010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95688 q = 0) : d97011 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d95688, d97011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95688, d97011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95785 q = 0) : d97082 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95785, d97082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6233 q selected
    | true =>
      simp only [d95785, d97082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6243 q selected
  have h7 (q : Pattern) (selected : d95803 q = 0) : d97100 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95803, d97100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6244 q selected
    | true =>
      simp only [d95803, d97100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6245 q selected
  have h8 (q : Pattern) (selected : d95804 q = 0) : d97101 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d95804, d97101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95804, d97101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d95805 q = 0) : d97102 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d95805, d97102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d95805, d97102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d95806 q = 0) : d97103 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d95806, d97103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95806, d97103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d95810 q = 0) : d97107 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95810, d97107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95810, d97107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6246 q selected
  have h12 (q : Pattern) (selected : d95812 q = 0) : d97109 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95812, d97109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95812, d97109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6247 q selected
  have h13 (q : Pattern) (selected : d95813 q = 0) : d97110 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d95813, d97110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d95813, d97110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d95814 q = 0) : d97111 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d95814, d97111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d95814, d97111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d95815 q = 0) : d97112 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d95815, d97112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d95815, d97112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d95816 q = 0) : d97113 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d95816, d97113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d95816, d97113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d95885 q = 0) : d97168 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95885, d97168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95885, d97168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6266 q selected
  have h18 (q : Pattern) (selected : d95896 q = 0) : d97175 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95896, d97175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95896, d97175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6268 q selected
  have h19 (q : Pattern) (selected : d95897 q = 0) : d97176 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d95897, d97176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d95897, d97176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d95898 q = 0) : d97177 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d95898, d97177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d95898, d97177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d95899 q = 0) : d97178 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d95899, d97178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d95899, d97178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d95900 q = 0) : d97179 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d95900, d97179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d95900, d97179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d95901 q = 0) : d97180 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95901, d97180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d95901, d97180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro6270 (p : Pattern) (selected : d95907 p = 0) : d97186 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95902 q = 0) : d97181 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d95902, d97181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95902, d97181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6269 q selected
  have h2 (q : Pattern) (selected : d95903 q = 0) : d97182 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d95903, d97182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95903, d97182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95904 q = 0) : d97183 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d95904, d97183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95904, d97183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95905 q = 0) : d97184 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d95905, d97184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95905, d97184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95906 q = 0) : d97185 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d95906, d97185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95906, d97185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95907 q = 0) : d97186 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d95907, d97186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95907, d97186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6271 (p : Pattern) (selected : d2069 p = 0) : d53348 p = 1 := by
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
  have h4 (q : Pattern) (selected : d2056 q = 0) : d53335 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2065 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2066 q = 0) : d53345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2067 q = 0) : d53346 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2067, d53346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2068 q = 0) : d53347 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d53347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2068, d53347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2069 q = 0) : d53348 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2069, d53348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2069, d53348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro6272 (p : Pattern) (selected : d2071 p = 0) : d53350 p = 1 := by
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
  have h4 (q : Pattern) (selected : d2068 q = 0) : d53347 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2068, d53347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2068, d53347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2071 q = 0) : d53350 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2071, d53350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2071, d53350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6273 (p : Pattern) (selected : d2084 p = 0) : d53363 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2080 q = 0) : d53359 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2080, d53359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro562 q selected
    | true =>
      simp only [d2080, d53359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2081 q = 0) : d53360 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2081, d53360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2081, d53360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2082 q = 0) : d53361 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2082, d53361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2082, d53361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2083 q = 0) : d53362 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2083, d53362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2083, d53362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2084 q = 0) : d53363 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2084, d53363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2084, d53363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6274 (p : Pattern) (selected : d95919 p = 0) : d97198 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95912 q = 0) : d97191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95912, d97191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6271 q selected
    | true =>
      simp only [d95912, d97191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6272 q selected
  have h2 (q : Pattern) (selected : d95913 q = 0) : d97192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95913, d97192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95913, d97192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95914 q = 0) : d97193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95914, d97193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95914, d97193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95915 q = 0) : d97194 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95915, d97194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6272 q selected
    | true =>
      simp only [d95915, d97194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6273 q selected
  have h5 (q : Pattern) (selected : d95916 q = 0) : d97195 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95916, d97195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95916, d97195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95917 q = 0) : d97196 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95917, d97196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95917, d97196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95918 q = 0) : d97197 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95918, d97197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95918, d97197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95919 q = 0) : d97198 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95919, d97198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95919, d97198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6275 (p : Pattern) (selected : d95923 p = 0) : d97202 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95915 q = 0) : d97194 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95915, d97194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6272 q selected
    | true =>
      simp only [d95915, d97194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6273 q selected
  have h2 (q : Pattern) (selected : d95916 q = 0) : d97195 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95916, d97195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95916, d97195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95917 q = 0) : d97196 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95917, d97196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95917, d97196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95922 q = 0) : d97201 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95922, d97201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95922, d97201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95923 q = 0) : d97202 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95923, d97202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95923, d97202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6276 (p : Pattern) (selected : d95929 p = 0) : d97208 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95920 q = 0) : d97199 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95920, d97199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6274 q selected
    | true =>
      simp only [d95920, d97199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95921 q = 0) : d97200 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95921, d97200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95921, d97200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95924 q = 0) : d97203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6275 q selected
    | true =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95925 q = 0) : d97204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95926 q = 0) : d97205 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95926, d97205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95926, d97205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95927 q = 0) : d97206 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95927, d97206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95927, d97206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95928 q = 0) : d97207 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95928, d97207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95928, d97207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95929 q = 0) : d97208 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95929, d97208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95929, d97208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6277 (p : Pattern) (selected : d95933 p = 0) : d97212 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95924 q = 0) : d97203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6275 q selected
    | true =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95925 q = 0) : d97204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95930 q = 0) : d97209 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95930, d97209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95930, d97209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95931 q = 0) : d97210 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95931, d97210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95931, d97210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95932 q = 0) : d97211 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95932, d97211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95932, d97211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d95933 q = 0) : d97212 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95933, d97212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95933, d97212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6278 (p : Pattern) (selected : d95939 p = 0) : d97218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95934 q = 0) : d97213 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95934, d97213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6276 q selected
    | true =>
      simp only [d95934, d97213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6277 q selected
  have h2 (q : Pattern) (selected : d95935 q = 0) : d97214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95935, d97214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95935, d97214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95936 q = 0) : d97215 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95936, d97215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95936, d97215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95937 q = 0) : d97216 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95937, d97216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95937, d97216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95938 q = 0) : d97217 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95938, d97217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95938, d97217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95939 q = 0) : d97218 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d95939, d97218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95939, d97218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6279 (p : Pattern) (selected : d95942 p = 0) : d97221 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95920 q = 0) : d97199 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95920, d97199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6274 q selected
    | true =>
      simp only [d95920, d97199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95921 q = 0) : d97200 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95921, d97200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95921, d97200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95924 q = 0) : d97203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6275 q selected
    | true =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95925 q = 0) : d97204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95926 q = 0) : d97205 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95926, d97205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95926, d97205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95927 q = 0) : d97206 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95927, d97206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95927, d97206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95928 q = 0) : d97207 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95928, d97207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95928, d97207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95942 q = 0) : d97221 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95942, d97221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95942, d97221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6280 (p : Pattern) (selected : d95943 p = 0) : d97222 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95924 q = 0) : d97203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6275 q selected
    | true =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95925 q = 0) : d97204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95930 q = 0) : d97209 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95930, d97209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95930, d97209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95931 q = 0) : d97210 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95931, d97210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95931, d97210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95932 q = 0) : d97211 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95932, d97211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95932, d97211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d95943 q = 0) : d97222 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95943, d97222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95943, d97222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6281 (p : Pattern) (selected : d95949 p = 0) : d97228 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95934 q = 0) : d97213 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95934, d97213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6276 q selected
    | true =>
      simp only [d95934, d97213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6277 q selected
  have h2 (q : Pattern) (selected : d95935 q = 0) : d97214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95935, d97214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95935, d97214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95936 q = 0) : d97215 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95936, d97215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95936, d97215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95937 q = 0) : d97216 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95937, d97216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95937, d97216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95938 q = 0) : d97217 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95938, d97217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95938, d97217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95944 q = 0) : d97223 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95944, d97223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6279 q selected
    | true =>
      simp only [d95944, d97223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6280 q selected
  have h7 (q : Pattern) (selected : d95945 q = 0) : d97224 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95945, d97224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95945, d97224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95946 q = 0) : d97225 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95946, d97225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95946, d97225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d95947 q = 0) : d97226 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95947, d97226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95947, d97226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d95948 q = 0) : d97227 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95948, d97227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95948, d97227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d95949 q = 0) : d97228 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d95949, d97228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95949, d97228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro6282 (p : Pattern) (selected : d95954 p = 0) : d97233 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95920 q = 0) : d97199 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95920, d97199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6274 q selected
    | true =>
      simp only [d95920, d97199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95921 q = 0) : d97200 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95921, d97200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95921, d97200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95924 q = 0) : d97203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6275 q selected
    | true =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95925 q = 0) : d97204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95926 q = 0) : d97205 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95926, d97205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95926, d97205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95927 q = 0) : d97206 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95927, d97206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95927, d97206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95953 q = 0) : d97232 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95953, d97232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95953, d97232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95954 q = 0) : d97233 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95954, d97233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95954, d97233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6283 (p : Pattern) (selected : d95956 p = 0) : d97235 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95924 q = 0) : d97203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6275 q selected
    | true =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95925 q = 0) : d97204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95930 q = 0) : d97209 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95930, d97209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95930, d97209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95931 q = 0) : d97210 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95931, d97210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95931, d97210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95955 q = 0) : d97234 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95955, d97234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95955, d97234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95956 q = 0) : d97235 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95956, d97235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95956, d97235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6284 (p : Pattern) (selected : d95963 p = 0) : d97242 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95920 q = 0) : d97199 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95920, d97199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6274 q selected
    | true =>
      simp only [d95920, d97199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95921 q = 0) : d97200 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95921, d97200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95921, d97200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95924 q = 0) : d97203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6275 q selected
    | true =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95925 q = 0) : d97204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95926 q = 0) : d97205 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95926, d97205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95926, d97205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95961 q = 0) : d97240 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95961, d97240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95961, d97240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95962 q = 0) : d97241 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95962, d97241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95962, d97241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95963 q = 0) : d97242 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95963, d97242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95963, d97242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6285 (p : Pattern) (selected : d95966 p = 0) : d97245 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95924 q = 0) : d97203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6275 q selected
    | true =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95925 q = 0) : d97204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95930 q = 0) : d97209 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95930, d97209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95930, d97209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95964 q = 0) : d97243 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95964, d97243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95964, d97243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95965 q = 0) : d97244 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95965, d97244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95965, d97244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d95966 q = 0) : d97245 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95966, d97245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95966, d97245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6286 (p : Pattern) (selected : d2057 p = 0) : d53336 p = 1 := by
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
  have h4 (q : Pattern) (selected : d2038 q = 0) : d53317 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2038, d53317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2038, d53317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2053 q = 0) : d53332 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro558 q selected
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2054 q = 0) : d53333 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2055 q = 0) : d53334 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2055, d53334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2056 q = 0) : d53335 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2056, d53335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2057 q = 0) : d53336 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2057, d53336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2057, d53336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro6287 (p : Pattern) (selected : d95974 p = 0) : d97253 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95970 q = 0) : d97249 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95970, d97249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6286 q selected
    | true =>
      simp only [d95970, d97249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6271 q selected
  have h2 (q : Pattern) (selected : d95971 q = 0) : d97250 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95971, d97250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95971, d97250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95972 q = 0) : d97251 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95972, d97251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95972, d97251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95912 q = 0) : d97191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95912, d97191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6271 q selected
    | true =>
      simp only [d95912, d97191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6272 q selected
  have h5 (q : Pattern) (selected : d95913 q = 0) : d97192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95913, d97192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95913, d97192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95914 q = 0) : d97193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95914, d97193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95914, d97193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95973 q = 0) : d97252 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95973, d97252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95973, d97252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95974 q = 0) : d97253 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95974, d97253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95974, d97253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6288 (p : Pattern) (selected : d95978 p = 0) : d97257 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95912 q = 0) : d97191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95912, d97191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6271 q selected
    | true =>
      simp only [d95912, d97191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6272 q selected
  have h2 (q : Pattern) (selected : d95913 q = 0) : d97192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95913, d97192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95913, d97192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95914 q = 0) : d97193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95914, d97193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95914, d97193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95977 q = 0) : d97256 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95977, d97256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95977, d97256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95978 q = 0) : d97257 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95978, d97257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95978, d97257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6289 (p : Pattern) (selected : d95984 p = 0) : d97263 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95975 q = 0) : d97254 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95975, d97254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6287 q selected
    | true =>
      simp only [d95975, d97254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95976 q = 0) : d97255 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95976, d97255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95976, d97255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95979 q = 0) : d97258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95979, d97258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6288 q selected
    | true =>
      simp only [d95979, d97258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95980 q = 0) : d97259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95980, d97259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95980, d97259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95981 q = 0) : d97260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95981, d97260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95981, d97260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95982 q = 0) : d97261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95982, d97261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95982, d97261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95983 q = 0) : d97262 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95983, d97262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95983, d97262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95984 q = 0) : d97263 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95984, d97263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95984, d97263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6290 (p : Pattern) (selected : d95988 p = 0) : d97267 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95979 q = 0) : d97258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95979, d97258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6288 q selected
    | true =>
      simp only [d95979, d97258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95980 q = 0) : d97259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95980, d97259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95980, d97259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95924 q = 0) : d97203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6275 q selected
    | true =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95925 q = 0) : d97204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95985 q = 0) : d97264 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95985, d97264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95985, d97264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95986 q = 0) : d97265 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95986, d97265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95986, d97265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95987 q = 0) : d97266 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95987, d97266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95987, d97266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95988 q = 0) : d97267 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95988, d97267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95988, d97267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6291 (p : Pattern) (selected : d2235 p = 0) : d53348 p = 1 := by
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
  have h4 (q : Pattern) (selected : d2222 q = 0) : d53335 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2222, d53335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2222, d53335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2231 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro593 q selected
    | true =>
      simp only [d2231, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2232 q = 0) : d53345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2232, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2233 q = 0) : d53346 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2233, d53346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2233, d53346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2234 q = 0) : d53347 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2234, d53347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2234, d53347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2235 q = 0) : d53348 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2235, d53348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2235, d53348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro6292 (p : Pattern) (selected : d2237 p = 0) : d53350 p = 1 := by
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
  have h4 (q : Pattern) (selected : d2234 q = 0) : d53347 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2234, d53347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2234, d53347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2237 q = 0) : d53350 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2237, d53350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2237, d53350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6293 (p : Pattern) (selected : d2250 p = 0) : d53363 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2246 q = 0) : d53359 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2246, d53359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro596 q selected
    | true =>
      simp only [d2246, d53359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2247 q = 0) : d53360 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2247, d53360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2247, d53360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2248 q = 0) : d53361 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2248, d53361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2248, d53361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2249 q = 0) : d53362 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2249, d53362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2249, d53362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2250 q = 0) : d53363 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2250, d53363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2250, d53363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6294 (p : Pattern) (selected : d95997 p = 0) : d97198 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95990 q = 0) : d97191 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95990, d97191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6291 q selected
    | true =>
      simp only [d95990, d97191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6292 q selected
  have h2 (q : Pattern) (selected : d95991 q = 0) : d97192 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95991, d97192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95991, d97192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95992 q = 0) : d97193 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95992, d97193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95992, d97193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95993 q = 0) : d97194 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95993, d97194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6292 q selected
    | true =>
      simp only [d95993, d97194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6293 q selected
  have h5 (q : Pattern) (selected : d95994 q = 0) : d97195 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95994, d97195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95994, d97195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95995 q = 0) : d97196 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95995, d97196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95995, d97196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95996 q = 0) : d97197 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95996, d97197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95996, d97197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95997 q = 0) : d97198 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95997, d97198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95997, d97198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6295 (p : Pattern) (selected : d96001 p = 0) : d97202 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95993 q = 0) : d97194 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95993, d97194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6292 q selected
    | true =>
      simp only [d95993, d97194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6293 q selected
  have h2 (q : Pattern) (selected : d95994 q = 0) : d97195 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95994, d97195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95994, d97195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95995 q = 0) : d97196 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95995, d97196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95995, d97196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d96000 q = 0) : d97201 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96000, d97201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96000, d97201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96001 q = 0) : d97202 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96001, d97202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96001, d97202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6296 (p : Pattern) (selected : d96007 p = 0) : d97208 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95998 q = 0) : d97199 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95998, d97199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6294 q selected
    | true =>
      simp only [d95998, d97199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95999 q = 0) : d97200 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95999, d97200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95999, d97200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96002 q = 0) : d97203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96002, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6295 q selected
    | true =>
      simp only [d96002, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96003 q = 0) : d97204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96003, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96003, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d96004 q = 0) : d97205 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96004, d97205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96004, d97205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96005 q = 0) : d97206 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96005, d97206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96005, d97206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d96006 q = 0) : d97207 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96006, d97207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d96006, d97207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d96007 q = 0) : d97208 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96007, d97208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96007, d97208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6297 (p : Pattern) (selected : d96011 p = 0) : d97212 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96002 q = 0) : d97203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96002, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6295 q selected
    | true =>
      simp only [d96002, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96003 q = 0) : d97204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96003, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96003, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96008 q = 0) : d97209 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96008, d97209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96008, d97209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96009 q = 0) : d97210 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96009, d97210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96009, d97210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96010 q = 0) : d97211 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96010, d97211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96010, d97211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96011 q = 0) : d97212 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96011, d97212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96011, d97212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6298 (p : Pattern) (selected : d96017 p = 0) : d97273 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95920 q = 0) : d97199 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95920, d97199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6274 q selected
    | true =>
      simp only [d95920, d97199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95921 q = 0) : d97200 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95921, d97200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95921, d97200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96014 q = 0) : d97270 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96014, d97270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96014, d97270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96015 q = 0) : d97271 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96015, d97271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96015, d97271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96016 q = 0) : d97272 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96016, d97272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96016, d97272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96017 q = 0) : d97273 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96017, d97273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96017, d97273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6299 (p : Pattern) (selected : d96023 p = 0) : d97279 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95957 q = 0) : d97236 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95957, d97236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6282 q selected
    | true =>
      simp only [d95957, d97236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6283 q selected
  have h2 (q : Pattern) (selected : d95958 q = 0) : d97237 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95958, d97237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95958, d97237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95959 q = 0) : d97238 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95959, d97238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95959, d97238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95960 q = 0) : d97239 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95960, d97239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95960, d97239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95967 q = 0) : d97246 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95967, d97246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6284 q selected
    | true =>
      simp only [d95967, d97246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6285 q selected
  have h6 (q : Pattern) (selected : d95968 q = 0) : d97247 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95968, d97247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95968, d97247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95969 q = 0) : d97248 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95969, d97248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95969, d97248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95989 q = 0) : d97268 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95989, d97268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6289 q selected
    | true =>
      simp only [d95989, d97268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6290 q selected
  have h9 (q : Pattern) (selected : d96012 q = 0) : d97213 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96012, d97213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6296 q selected
    | true =>
      simp only [d96012, d97213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6297 q selected
  have h10 (q : Pattern) (selected : d96013 q = 0) : d97269 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96013, d97269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d96013, d97269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d96018 q = 0) : d97274 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96018, d97274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6298 q selected
    | true =>
      simp only [d96018, d97274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d96019 q = 0) : d97275 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96019, d97275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d96019, d97275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d96020 q = 0) : d97276 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96020, d97276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d96020, d97276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d96021 q = 0) : d97277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96021, d97277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d96021, d97277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d96022 q = 0) : d97278 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96022, d97278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96022, d97278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d96023 q = 0) : d97279 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96023, d97279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96023, d97279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro6300 (p : Pattern) (selected : d96024 p = 0) : d97280 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95920 q = 0) : d97199 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95920, d97199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6274 q selected
    | true =>
      simp only [d95920, d97199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95921 q = 0) : d97200 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95921, d97200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95921, d97200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95924 q = 0) : d97203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6275 q selected
    | true =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95925 q = 0) : d97204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95926 q = 0) : d97205 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95926, d97205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95926, d97205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95927 q = 0) : d97206 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95927, d97206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95927, d97206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95953 q = 0) : d97232 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95953, d97232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95953, d97232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d96024 q = 0) : d97280 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96024, d97280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d96024, d97280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6301 (p : Pattern) (selected : d96025 p = 0) : d97281 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95924 q = 0) : d97203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6275 q selected
    | true =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95925 q = 0) : d97204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95930 q = 0) : d97209 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95930, d97209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95930, d97209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95931 q = 0) : d97210 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95931, d97210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95931, d97210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95955 q = 0) : d97234 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95955, d97234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95955, d97234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96025 q = 0) : d97281 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96025, d97281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96025, d97281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6302 (p : Pattern) (selected : d96030 p = 0) : d97286 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95920 q = 0) : d97199 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95920, d97199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6274 q selected
    | true =>
      simp only [d95920, d97199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95921 q = 0) : d97200 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95921, d97200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95921, d97200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95924 q = 0) : d97203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6275 q selected
    | true =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95925 q = 0) : d97204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95926 q = 0) : d97205 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95926, d97205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95926, d97205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95961 q = 0) : d97240 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95961, d97240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95961, d97240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95962 q = 0) : d97241 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95962, d97241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95962, d97241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d96030 q = 0) : d97286 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96030, d97286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d96030, d97286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6303 (p : Pattern) (selected : d96031 p = 0) : d97287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95924 q = 0) : d97203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6275 q selected
    | true =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95925 q = 0) : d97204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95930 q = 0) : d97209 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95930, d97209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95930, d97209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95964 q = 0) : d97243 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95964, d97243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95964, d97243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95965 q = 0) : d97244 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95965, d97244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95965, d97244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96031 q = 0) : d97287 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96031, d97287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96031, d97287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6304 (p : Pattern) (selected : d96035 p = 0) : d97291 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95975 q = 0) : d97254 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95975, d97254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6287 q selected
    | true =>
      simp only [d95975, d97254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95976 q = 0) : d97255 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95976, d97255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95976, d97255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95979 q = 0) : d97258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95979, d97258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6288 q selected
    | true =>
      simp only [d95979, d97258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95980 q = 0) : d97259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95980, d97259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95980, d97259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95981 q = 0) : d97260 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95981, d97260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95981, d97260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95982 q = 0) : d97261 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95982, d97261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95982, d97261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95983 q = 0) : d97262 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95983, d97262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95983, d97262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d96035 q = 0) : d97291 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96035, d97291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d96035, d97291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6305 (p : Pattern) (selected : d96036 p = 0) : d97292 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95979 q = 0) : d97258 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95979, d97258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6288 q selected
    | true =>
      simp only [d95979, d97258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95980 q = 0) : d97259 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95980, d97259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95980, d97259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95924 q = 0) : d97203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6275 q selected
    | true =>
      simp only [d95924, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95925 q = 0) : d97204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95925, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95985 q = 0) : d97264 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95985, d97264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95985, d97264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95986 q = 0) : d97265 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95986, d97265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95986, d97265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95987 q = 0) : d97266 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95987, d97266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95987, d97266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d96036 q = 0) : d97292 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96036, d97292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d96036, d97292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6306 (p : Pattern) (selected : d96038 p = 0) : d97221 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95998 q = 0) : d97199 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95998, d97199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6294 q selected
    | true =>
      simp only [d95998, d97199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95999 q = 0) : d97200 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95999, d97200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95999, d97200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96002 q = 0) : d97203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96002, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6295 q selected
    | true =>
      simp only [d96002, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96003 q = 0) : d97204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96003, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96003, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d96004 q = 0) : d97205 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96004, d97205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96004, d97205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96005 q = 0) : d97206 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96005, d97206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96005, d97206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d96006 q = 0) : d97207 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96006, d97207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d96006, d97207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d96038 q = 0) : d97221 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96038, d97221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d96038, d97221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6307 (p : Pattern) (selected : d96039 p = 0) : d97222 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96002 q = 0) : d97203 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96002, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6295 q selected
    | true =>
      simp only [d96002, d97203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96003 q = 0) : d97204 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96003, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96003, d97204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96008 q = 0) : d97209 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96008, d97209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96008, d97209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96009 q = 0) : d97210 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96009, d97210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96009, d97210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96010 q = 0) : d97211 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96010, d97211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96010, d97211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96039 q = 0) : d97222 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96039, d97222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96039, d97222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6308 (p : Pattern) (selected : d96042 p = 0) : d97295 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95920 q = 0) : d97199 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95920, d97199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6274 q selected
    | true =>
      simp only [d95920, d97199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95921 q = 0) : d97200 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95921, d97200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95921, d97200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96014 q = 0) : d97270 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96014, d97270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96014, d97270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96015 q = 0) : d97271 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96015, d97271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96015, d97271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96016 q = 0) : d97272 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96016, d97272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96016, d97272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96042 q = 0) : d97295 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96042, d97295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96042, d97295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6309 (p : Pattern) (selected : d96048 p = 0) : d97301 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95957 q = 0) : d97236 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95957, d97236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6282 q selected
    | true =>
      simp only [d95957, d97236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6283 q selected
  have h2 (q : Pattern) (selected : d95958 q = 0) : d97237 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95958, d97237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95958, d97237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95959 q = 0) : d97238 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95959, d97238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95959, d97238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95960 q = 0) : d97239 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95960, d97239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95960, d97239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95967 q = 0) : d97246 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95967, d97246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6284 q selected
    | true =>
      simp only [d95967, d97246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6285 q selected
  have h6 (q : Pattern) (selected : d95968 q = 0) : d97247 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95968, d97247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95968, d97247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95969 q = 0) : d97248 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95969, d97248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95969, d97248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95989 q = 0) : d97268 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95989, d97268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6289 q selected
    | true =>
      simp only [d95989, d97268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6290 q selected
  have h9 (q : Pattern) (selected : d96012 q = 0) : d97213 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96012, d97213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6296 q selected
    | true =>
      simp only [d96012, d97213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6297 q selected
  have h10 (q : Pattern) (selected : d96013 q = 0) : d97269 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96013, d97269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d96013, d97269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d96018 q = 0) : d97274 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96018, d97274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6298 q selected
    | true =>
      simp only [d96018, d97274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d96019 q = 0) : d97275 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96019, d97275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d96019, d97275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d96020 q = 0) : d97276 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96020, d97276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d96020, d97276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d96021 q = 0) : d97277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96021, d97277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d96021, d97277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d96022 q = 0) : d97278 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96022, d97278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96022, d97278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d96026 q = 0) : d97282 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96026, d97282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6300 q selected
    | true =>
      simp only [d96026, d97282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6301 q selected
  have h17 (q : Pattern) (selected : d96027 q = 0) : d97283 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96027, d97283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96027, d97283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d96028 q = 0) : d97284 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96028, d97284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d96028, d97284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d96029 q = 0) : d97285 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96029, d97285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96029, d97285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d96032 q = 0) : d97288 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96032, d97288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6302 q selected
    | true =>
      simp only [d96032, d97288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6303 q selected
  have h21 (q : Pattern) (selected : d96033 q = 0) : d97289 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96033, d97289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96033, d97289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d96034 q = 0) : d97290 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96034, d97290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d96034, d97290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d96037 q = 0) : d97293 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96037, d97293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6304 q selected
    | true =>
      simp only [d96037, d97293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6305 q selected
  have h24 (q : Pattern) (selected : d96040 q = 0) : d97223 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96040, d97223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6306 q selected
    | true =>
      simp only [d96040, d97223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6307 q selected
  have h25 (q : Pattern) (selected : d96041 q = 0) : d97294 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96041, d97294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d96041, d97294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d96043 q = 0) : d97296 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96043, d97296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6308 q selected
    | true =>
      simp only [d96043, d97296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d96044 q = 0) : d97297 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96044, d97297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d96044, d97297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d96045 q = 0) : d97298 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96045, d97298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d96045, d97298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d96046 q = 0) : d97299 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96046, d97299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d96046, d97299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d96047 q = 0) : d97300 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96047, d97300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d96047, d97300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d96048 q = 0) : d97301 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96048, d97301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d96048, d97301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro6310 (p : Pattern) (selected : d96060 p = 0) : d97313 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96050 q = 0) : d97303 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96050, d97303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6290 q selected
    | true =>
      simp only [d96050, d97303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6277 q selected
  have h2 (q : Pattern) (selected : d96051 q = 0) : d97304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96051, d97304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96051, d97304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96052 q = 0) : d97305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96052, d97305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96052, d97305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96053 q = 0) : d97306 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96053, d97306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96053, d97306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d96054 q = 0) : d97307 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96054, d97307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96054, d97307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96055 q = 0) : d97308 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96055, d97308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6277 q selected
    | true =>
      simp only [d96055, d97308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d96056 q = 0) : d97309 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96056, d97309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96056, d97309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d96057 q = 0) : d97310 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96057, d97310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d96057, d97310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d96058 q = 0) : d97311 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96058, d97311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96058, d97311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d96059 q = 0) : d97312 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96059, d97312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96059, d97312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d96060 q = 0) : d97313 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96060, d97313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96060, d97313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro6311 (p : Pattern) (selected : d96066 p = 0) : d97319 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96055 q = 0) : d97308 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96055, d97308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6277 q selected
    | true =>
      simp only [d96055, d97308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96056 q = 0) : d97309 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96056, d97309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96056, d97309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96057 q = 0) : d97310 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96057, d97310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96057, d97310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96058 q = 0) : d97311 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96058, d97311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96058, d97311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d96059 q = 0) : d97312 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96059, d97312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96059, d97312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96061 q = 0) : d97314 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96061, d97314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6280 q selected
    | true =>
      simp only [d96061, d97314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d96062 q = 0) : d97315 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96062, d97315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96062, d97315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d96063 q = 0) : d97316 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96063, d97316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d96063, d97316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d96064 q = 0) : d97317 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96064, d97317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96064, d97317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d96065 q = 0) : d97318 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96065, d97318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96065, d97318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d96066 q = 0) : d97319 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96066, d97319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96066, d97319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro6312 (p : Pattern) (selected : d96073 p = 0) : d97326 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96037 q = 0) : d97293 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96037, d97293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6304 q selected
    | true =>
      simp only [d96037, d97293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6305 q selected
  have h2 (q : Pattern) (selected : d96040 q = 0) : d97223 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96040, d97223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6306 q selected
    | true =>
      simp only [d96040, d97223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6307 q selected
  have h3 (q : Pattern) (selected : d96041 q = 0) : d97294 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96041, d97294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96041, d97294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d96043 q = 0) : d97296 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96043, d97296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6308 q selected
    | true =>
      simp only [d96043, d97296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96044 q = 0) : d97297 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96044, d97297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96044, d97297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96045 q = 0) : d97298 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96045, d97298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96045, d97298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d96071 q = 0) : d97324 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96071, d97324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96071, d97324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d96072 q = 0) : d97325 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96072, d97325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96072, d97325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d96073 q = 0) : d97326 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96073, d97326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96073, d97326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro6313 (p : Pattern) (selected : d96075 p = 0) : d97328 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96061 q = 0) : d97314 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96061, d97314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6280 q selected
    | true =>
      simp only [d96061, d97314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96062 q = 0) : d97315 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96062, d97315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96062, d97315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96063 q = 0) : d97316 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96063, d97316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96063, d97316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96064 q = 0) : d97317 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96064, d97317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96064, d97317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d96065 q = 0) : d97318 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96065, d97318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96065, d97318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96075 q = 0) : d97328 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96075, d97328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96075, d97328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6314 (p : Pattern) (selected : d2344 p = 0) : d53509 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2335 q = 0) : d53500 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2335, d53500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro553 q selected
  have h2 (q : Pattern) (selected : d2035 q = 0) : d53314 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro553 q selected
    | true =>
      simp only [d2035, d53314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2336 q = 0) : d53501 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2336, d53501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2336, d53501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2036 q = 0) : d53315 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2036, d53315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2337 q = 0) : d53502 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2337, d53502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2337, d53502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2338 q = 0) : d53503 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2338, d53503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2338, d53503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2340 q = 0) : d53505 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro558 q selected
  have h8 (q : Pattern) (selected : d2053 q = 0) : d53332 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro558 q selected
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2341 q = 0) : d53506 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d2054 q = 0) : d53333 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d2342 q = 0) : d53507 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d2343 q = 0) : d53508 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d53508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2343, d53508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d2344 q = 0) : d53509 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2344, d53509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2344, d53509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro6315 (p : Pattern) (selected : d2350 p = 0) : d53515 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2340 q = 0) : d53505 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2340, d53505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro558 q selected
  have h2 (q : Pattern) (selected : d2053 q = 0) : d53332 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro558 q selected
    | true =>
      simp only [d2053, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2341 q = 0) : d53506 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2341, d53506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2054 q = 0) : d53333 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2054, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2342 q = 0) : d53507 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2342, d53507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2343 q = 0) : d53508 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2343, d53508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2343, d53508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2346 q = 0) : d53511 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
  have h8 (q : Pattern) (selected : d2065 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2347 q = 0) : d53512 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d2066 q = 0) : d53345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d2348 q = 0) : d53513 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d2349 q = 0) : d53514 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d53514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2349, d53514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d2350 q = 0) : d53515 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2350, d53515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2350, d53515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro6316 (p : Pattern) (selected : d2355 p = 0) : d53520 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2346 q = 0) : d53511 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2346, d53511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
  have h2 (q : Pattern) (selected : d2065 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro559 q selected
    | true =>
      simp only [d2065, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2347 q = 0) : d53512 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2347, d53512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2066 q = 0) : d53345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2066, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2348 q = 0) : d53513 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2348, d53513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2349 q = 0) : d53514 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2349, d53514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2349, d53514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2355 q = 0) : d53520 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2355, d53520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2355, d53520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro6317 (p : Pattern) (selected : d96088 p = 0) : d97341 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96081 q = 0) : d97334 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96081, d97334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6314 q selected
    | true =>
      simp only [d96081, d97334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6315 q selected
  have h2 (q : Pattern) (selected : d96082 q = 0) : d97335 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96082, d97335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96082, d97335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96083 q = 0) : d97336 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96083, d97336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96083, d97336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d96084 q = 0) : d97337 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96084, d97337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6315 q selected
    | true =>
      simp only [d96084, d97337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6316 q selected
  have h5 (q : Pattern) (selected : d96085 q = 0) : d97338 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96085, d97338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96085, d97338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96086 q = 0) : d97339 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96086, d97339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96086, d97339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d96087 q = 0) : d97340 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96087, d97340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96087, d97340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d96088 q = 0) : d97341 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96088, d97341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d96088, d97341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6318 (p : Pattern) (selected : d96092 p = 0) : d97345 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96084 q = 0) : d97337 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96084, d97337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6315 q selected
    | true =>
      simp only [d96084, d97337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6316 q selected
  have h2 (q : Pattern) (selected : d96085 q = 0) : d97338 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96085, d97338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96085, d97338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96086 q = 0) : d97339 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96086, d97339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96086, d97339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d96091 q = 0) : d97344 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96091, d97344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96091, d97344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96092 q = 0) : d97345 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96092, d97345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96092, d97345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6319 (p : Pattern) (selected : d96098 p = 0) : d97351 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96089 q = 0) : d97342 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96089, d97342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6317 q selected
    | true =>
      simp only [d96089, d97342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96090 q = 0) : d97343 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96090, d97343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96090, d97343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96093 q = 0) : d97346 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96093, d97346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6318 q selected
    | true =>
      simp only [d96093, d97346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96094 q = 0) : d97347 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96094, d97347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96094, d97347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d96095 q = 0) : d97348 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96095, d97348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96095, d97348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96096 q = 0) : d97349 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96096, d97349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96096, d97349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d96097 q = 0) : d97350 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96097, d97350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d96097, d97350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d96098 q = 0) : d97351 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96098, d97351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d96098, d97351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6320 (p : Pattern) (selected : d2365 p = 0) : d53530 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2361 q = 0) : d53526 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2361, d53526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2361, d53526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro562 q selected
  have h2 (q : Pattern) (selected : d2080 q = 0) : d53359 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2080, d53359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro562 q selected
    | true =>
      simp only [d2080, d53359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2362 q = 0) : d53527 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2362, d53527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2362, d53527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2081 q = 0) : d53360 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2081, d53360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2081, d53360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2363 q = 0) : d53528 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2363, d53528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2363, d53528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2364 q = 0) : d53529 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2364, d53529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2364, d53529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2365 q = 0) : d53530 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2365, d53530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2365, d53530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro6321 (p : Pattern) (selected : d96103 p = 0) : d97356 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96099 q = 0) : d97352 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96099, d97352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6316 q selected
    | true =>
      simp only [d96099, d97352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6320 q selected
  have h2 (q : Pattern) (selected : d96100 q = 0) : d97353 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96100, d97353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96100, d97353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96101 q = 0) : d97354 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96101, d97354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96101, d97354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d96102 q = 0) : d97355 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96102, d97355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96102, d97355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96103 q = 0) : d97356 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96103, d97356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96103, d97356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6322 (p : Pattern) (selected : d96109 p = 0) : d97362 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96093 q = 0) : d97346 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96093, d97346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6318 q selected
    | true =>
      simp only [d96093, d97346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96094 q = 0) : d97347 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96094, d97347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96094, d97347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96104 q = 0) : d97357 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96104, d97357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6321 q selected
    | true =>
      simp only [d96104, d97357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96105 q = 0) : d97358 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96105, d97358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96105, d97358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d96106 q = 0) : d97359 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96106, d97359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96106, d97359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96107 q = 0) : d97360 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96107, d97360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96107, d97360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d96108 q = 0) : d97361 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96108, d97361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d96108, d97361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d96109 q = 0) : d97362 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96109, d97362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d96109, d97362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6323 (p : Pattern) (selected : d2406 p = 0) : d53515 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2397 q = 0) : d53505 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2397, d53505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2397, d53505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro592 q selected
  have h2 (q : Pattern) (selected : d2219 q = 0) : d53332 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro592 q selected
    | true =>
      simp only [d2219, d53332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2398 q = 0) : d53506 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2398, d53506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2398, d53506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2220 q = 0) : d53333 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2220, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2220, d53333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2399 q = 0) : d53507 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2399, d53507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2399, d53507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2400 q = 0) : d53508 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2400, d53508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2400, d53508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2402 q = 0) : d53511 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2402, d53511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2402, d53511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro593 q selected
  have h8 (q : Pattern) (selected : d2231 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro593 q selected
    | true =>
      simp only [d2231, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2403 q = 0) : d53512 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2403, d53512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2403, d53512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d2232 q = 0) : d53345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2232, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d2404 q = 0) : d53513 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2404, d53513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d2404, d53513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d2405 q = 0) : d53514 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2405, d53514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2405, d53514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d2406 q = 0) : d53515 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2406, d53515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2406, d53515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro6324 (p : Pattern) (selected : d2408 p = 0) : d53520 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2402 q = 0) : d53511 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2402, d53511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2402, d53511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro593 q selected
  have h2 (q : Pattern) (selected : d2231 q = 0) : d53344 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro593 q selected
    | true =>
      simp only [d2231, d53344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2403 q = 0) : d53512 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2403, d53512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2403, d53512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2232 q = 0) : d53345 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2232, d53345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2404 q = 0) : d53513 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2404, d53513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2404, d53513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2405 q = 0) : d53514 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2405, d53514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2405, d53514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2408 q = 0) : d53520 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2408, d53520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2408, d53520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro6325 (p : Pattern) (selected : d2417 p = 0) : d53530 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2413 q = 0) : d53526 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2413, d53526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2413, d53526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro596 q selected
  have h2 (q : Pattern) (selected : d2246 q = 0) : d53359 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2246, d53359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro596 q selected
    | true =>
      simp only [d2246, d53359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2414 q = 0) : d53527 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2414, d53527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2414, d53527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2247 q = 0) : d53360 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2247, d53360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2247, d53360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2415 q = 0) : d53528 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2415, d53528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2415, d53528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2416 q = 0) : d53529 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2416, d53529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2416, d53529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2417 q = 0) : d53530 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2417, d53530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2417, d53530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro6326 (p : Pattern) (selected : d96118 p = 0) : d97365 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96111 q = 0) : d97337 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96111, d97337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6323 q selected
    | true =>
      simp only [d96111, d97337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6324 q selected
  have h2 (q : Pattern) (selected : d96112 q = 0) : d97338 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96112, d97338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96112, d97338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96113 q = 0) : d97339 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96113, d97339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96113, d97339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d96114 q = 0) : d97352 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96114, d97352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6324 q selected
    | true =>
      simp only [d96114, d97352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6325 q selected
  have h5 (q : Pattern) (selected : d96115 q = 0) : d97353 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96115, d97353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96115, d97353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96116 q = 0) : d97354 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96116, d97354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96116, d97354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d96117 q = 0) : d97364 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96117, d97364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96117, d97364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d96118 q = 0) : d97365 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96118, d97365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d96118, d97365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6327 (p : Pattern) (selected : d96122 p = 0) : d97356 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96114 q = 0) : d97352 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96114, d97352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6324 q selected
    | true =>
      simp only [d96114, d97352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6325 q selected
  have h2 (q : Pattern) (selected : d96115 q = 0) : d97353 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96115, d97353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96115, d97353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96116 q = 0) : d97354 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96116, d97354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96116, d97354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d96121 q = 0) : d97355 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96121, d97355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96121, d97355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96122 q = 0) : d97356 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96122, d97356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96122, d97356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6328 (p : Pattern) (selected : d96128 p = 0) : d97371 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96119 q = 0) : d97366 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96119, d97366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6326 q selected
    | true =>
      simp only [d96119, d97366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96120 q = 0) : d97367 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96120, d97367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96120, d97367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96123 q = 0) : d97357 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96123, d97357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6327 q selected
    | true =>
      simp only [d96123, d97357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96124 q = 0) : d97358 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96124, d97358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96124, d97358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d96125 q = 0) : d97368 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96125, d97368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96125, d97368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96126 q = 0) : d97369 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96126, d97369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96126, d97369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d96127 q = 0) : d97370 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96127, d97370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d96127, d97370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d96128 q = 0) : d97371 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96128, d97371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d96128, d97371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6329 (p : Pattern) (selected : d96132 p = 0) : d97375 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96123 q = 0) : d97357 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96123, d97357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6327 q selected
    | true =>
      simp only [d96123, d97357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96124 q = 0) : d97358 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96124, d97358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96124, d97358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96129 q = 0) : d97372 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96129, d97372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96129, d97372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96130 q = 0) : d97373 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96130, d97373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96130, d97373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96131 q = 0) : d97374 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96131, d97374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96131, d97374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96132 q = 0) : d97375 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96132, d97375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96132, d97375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6330 (p : Pattern) (selected : d96136 p = 0) : d97365 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96084 q = 0) : d97337 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96084, d97337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6315 q selected
    | true =>
      simp only [d96084, d97337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6316 q selected
  have h2 (q : Pattern) (selected : d96085 q = 0) : d97338 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96085, d97338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96085, d97338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96086 q = 0) : d97339 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96086, d97339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96086, d97339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d96099 q = 0) : d97352 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96099, d97352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6316 q selected
    | true =>
      simp only [d96099, d97352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6320 q selected
  have h5 (q : Pattern) (selected : d96100 q = 0) : d97353 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96100, d97353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96100, d97353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96101 q = 0) : d97354 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96101, d97354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96101, d97354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d96135 q = 0) : d97364 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96135, d97364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96135, d97364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d96136 q = 0) : d97365 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96136, d97365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d96136, d97365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6331 (p : Pattern) (selected : d96142 p = 0) : d97381 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96137 q = 0) : d97366 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96137, d97366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6330 q selected
    | true =>
      simp only [d96137, d97366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96138 q = 0) : d97367 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96138, d97367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96138, d97367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96139 q = 0) : d97378 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96139, d97378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96139, d97378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96140 q = 0) : d97379 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96140, d97379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96140, d97379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96141 q = 0) : d97380 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96141, d97380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96141, d97380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96142 q = 0) : d97381 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96142, d97381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96142, d97381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6332 (p : Pattern) (selected : d96148 p = 0) : d97387 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96110 q = 0) : d97363 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96110, d97363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6319 q selected
    | true =>
      simp only [d96110, d97363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6322 q selected
  have h2 (q : Pattern) (selected : d96133 q = 0) : d97376 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96133, d97376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6328 q selected
    | true =>
      simp only [d96133, d97376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6329 q selected
  have h3 (q : Pattern) (selected : d96134 q = 0) : d97377 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96134, d97377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96134, d97377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d96143 q = 0) : d97382 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96143, d97382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6331 q selected
    | true =>
      simp only [d96143, d97382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96144 q = 0) : d97383 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96144, d97383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96144, d97383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96145 q = 0) : d97384 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96145, d97384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96145, d97384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d96146 q = 0) : d97385 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96146, d97385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96146, d97385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d96147 q = 0) : d97386 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96147, d97386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96147, d97386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d96148 q = 0) : d97387 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96148, d97387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96148, d97387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro6333 (p : Pattern) (selected : d96153 p = 0) : d97375 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96104 q = 0) : d97357 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96104, d97357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6321 q selected
    | true =>
      simp only [d96104, d97357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96105 q = 0) : d97358 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96105, d97358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96105, d97358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96150 q = 0) : d97372 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96150, d97372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96150, d97372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96151 q = 0) : d97373 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96151, d97373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96151, d97373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96152 q = 0) : d97374 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96152, d97374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96152, d97374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96153 q = 0) : d97375 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96153, d97375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96153, d97375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6334 (p : Pattern) (selected : d96159 p = 0) : d97394 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96154 q = 0) : d97389 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96154, d97389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6333 q selected
    | true =>
      simp only [d96154, d97389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96155 q = 0) : d97390 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96155, d97390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96155, d97390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96156 q = 0) : d97391 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96156, d97391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96156, d97391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96157 q = 0) : d97392 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96157, d97392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96157, d97392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d96158 q = 0) : d97393 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96158, d97393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96158, d97393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96159 q = 0) : d97394 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96159, d97394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96159, d97394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6335 (p : Pattern) (selected : d96165 p = 0) : d97400 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d95940 q = 0) : d97219 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95940, d97219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95940, d97219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6278 q selected
  have h2 (q : Pattern) (selected : d95941 q = 0) : d97220 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d95941, d97220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95941, d97220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d95950 q = 0) : d97229 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95950, d97229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6278 q selected
    | true =>
      simp only [d95950, d97229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6281 q selected
  have h4 (q : Pattern) (selected : d95951 q = 0) : d97230 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d95951, d97230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95951, d97230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95952 q = 0) : d97231 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d95952, d97231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95952, d97231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96049 q = 0) : d97302 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96049, d97302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6299 q selected
    | true =>
      simp only [d96049, d97302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6309 q selected
  have h7 (q : Pattern) (selected : d96067 q = 0) : d97320 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96067, d97320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6310 q selected
    | true =>
      simp only [d96067, d97320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6311 q selected
  have h8 (q : Pattern) (selected : d96068 q = 0) : d97321 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96068, d97321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d96068, d97321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d96069 q = 0) : d97322 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96069, d97322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d96069, d97322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d96070 q = 0) : d97323 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96070, d97323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96070, d97323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d96074 q = 0) : d97327 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96074, d97327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96074, d97327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6312 q selected
  have h12 (q : Pattern) (selected : d96076 q = 0) : d97329 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96076, d97329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96076, d97329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6313 q selected
  have h13 (q : Pattern) (selected : d96077 q = 0) : d97330 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96077, d97330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d96077, d97330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d96078 q = 0) : d97331 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96078, d97331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d96078, d97331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d96079 q = 0) : d97332 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96079, d97332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d96079, d97332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d96080 q = 0) : d97333 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96080, d97333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d96080, d97333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d96149 q = 0) : d97388 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96149, d97388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96149, d97388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6332 q selected
  have h18 (q : Pattern) (selected : d96160 q = 0) : d97395 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96160, d97395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96160, d97395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6334 q selected
  have h19 (q : Pattern) (selected : d96161 q = 0) : d97396 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96161, d97396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d96161, d97396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d96162 q = 0) : d97397 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96162, d97397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d96162, d97397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d96163 q = 0) : d97398 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96163, d97398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d96163, d97398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d96164 q = 0) : d97399 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96164, d97399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d96164, d97399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d96165 q = 0) : d97400 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d96165, d97400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d96165, d97400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro6336 (p : Pattern) (selected : d96171 p = 0) : d97406 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96166 q = 0) : d97401 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96166, d97401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96166, d97401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6335 q selected
  have h2 (q : Pattern) (selected : d96167 q = 0) : d97402 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d96167, d97402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96167, d97402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96168 q = 0) : d97403 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d96168, d97403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96168, d97403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d96169 q = 0) : d97404 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d96169, d97404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96169, d97404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d96170 q = 0) : d97405 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d96170, d97405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96170, d97405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96171 q = 0) : d97406 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d96171, d97406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96171, d97406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6337 (p : Pattern) (selected : d96177 p = 0) : d97412 p = 1 := by
  have h0 (q : Pattern) (selected : d95122 q = 0) : d96533 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d95122, d96533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6039 q selected
    | true =>
      simp only [d95122, d96533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6076 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d95383 q = 0) : d96750 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d95383, d96750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95383, d96750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6138 q selected
  have h3 (q : Pattern) (selected : d95384 q = 0) : d96751 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d95384, d96751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95384, d96751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95645 q = 0) : d96968 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d95645, d96968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95645, d96968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6204 q selected
  have h5 (q : Pattern) (selected : d95646 q = 0) : d96969 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d95646, d96969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95646, d96969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95647 q = 0) : d96970 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d95647, d96970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95647, d96970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95908 q = 0) : d97187 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d95908, d97187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95908, d97187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6270 q selected
  have h8 (q : Pattern) (selected : d95909 q = 0) : d97188 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d95909, d97188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95909, d97188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d95910 q = 0) : d97189 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d95910, d97189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95910, d97189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d95911 q = 0) : d97190 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d95911, d97190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95911, d97190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d96172 q = 0) : d97407 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d96172, d97407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96172, d97407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6336 q selected
  have h12 (q : Pattern) (selected : d96173 q = 0) : d97408 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d96173, d97408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96173, d97408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d96174 q = 0) : d97409 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d96174, d97409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96174, d97409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d96175 q = 0) : d97410 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d96175, d97410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96175, d97410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d96176 q = 0) : d97411 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d96176, d97411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d96176, d97411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d96177 q = 0) : d97412 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d96177, d97412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d96177, d97412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro6338 (p : Pattern) (selected : d96183 p = 0) : d97418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96178 q = 0) : d97413 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d96178, d97413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6337 q selected
    | true =>
      simp only [d96178, d97413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96179 q = 0) : d97414 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d96179, d97414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96179, d97414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d96180 q = 0) : d97415 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d96180, d97415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96180, d97415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96181 q = 0) : d97416 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d96181, d97416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96181, d97416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96182 q = 0) : d97417 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d96182, d97417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96182, d97417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96183 q = 0) : d97418 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d96183, d97418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96183, d97418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6339 (p : Pattern) (selected : d96189 p = 0) : d97424 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96184 q = 0) : d97419 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d96184, d97419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6338 q selected
    | true =>
      simp only [d96184, d97419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96185 q = 0) : d97420 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d96185, d97420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96185, d97420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d96186 q = 0) : d97421 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d96186, d97421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96186, d97421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96187 q = 0) : d97422 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d96187, d97422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96187, d97422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96188 q = 0) : d97423 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d96188, d97423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96188, d97423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96189 q = 0) : d97424 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d96189, d97424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96189, d97424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6340 (p : Pattern) (selected : d96195 p = 0) : d97430 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96190 q = 0) : d97425 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d96190, d97425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6339 q selected
    | true =>
      simp only [d96190, d97425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96191 q = 0) : d97426 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d96191, d97426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96191, d97426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d96192 q = 0) : d97427 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d96192, d97427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96192, d97427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96193 q = 0) : d97428 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d96193, d97428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96193, d97428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96194 q = 0) : d97429 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d96194, d97429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96194, d97429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96195 q = 0) : d97430 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d96195, d97430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96195, d97430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6341 (p : Pattern) (selected : d96201 p = 0) : d97436 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96196 q = 0) : d97431 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d96196, d97431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6340 q selected
    | true =>
      simp only [d96196, d97431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96197 q = 0) : d97432 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d96197, d97432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96197, d97432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d96198 q = 0) : d97433 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d96198, d97433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96198, d97433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96199 q = 0) : d97434 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d96199, d97434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96199, d97434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96200 q = 0) : d97435 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d96200, d97435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96200, d97435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96201 q = 0) : d97436 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d96201, d97436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96201, d97436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6342 (p : Pattern) (selected : d96207 p = 0) : d97442 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96202 q = 0) : d97437 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d96202, d97437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6341 q selected
    | true =>
      simp only [d96202, d97437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96203 q = 0) : d97438 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d96203, d97438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96203, d97438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d96204 q = 0) : d97439 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d96204, d97439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96204, d97439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96205 q = 0) : d97440 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d96205, d97440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96205, d97440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96206 q = 0) : d97441 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d96206, d97441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96206, d97441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96207 q = 0) : d97442 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d96207, d97442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96207, d97442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6343 (p : Pattern) (selected : d96213 p = 0) : d97448 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96208 q = 0) : d97443 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d96208, d97443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6342 q selected
    | true =>
      simp only [d96208, d97443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96209 q = 0) : d97444 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d96209, d97444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96209, d97444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d96210 q = 0) : d97445 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d96210, d97445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96210, d97445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96211 q = 0) : d97446 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d96211, d97446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96211, d97446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96212 q = 0) : d97447 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d96212, d97447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96212, d97447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96213 q = 0) : d97448 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d96213, d97448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96213, d97448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6344 (p : Pattern) (selected : d96219 p = 0) : d97454 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d96214 q = 0) : d97449 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d96214, d97449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6343 q selected
    | true =>
      simp only [d96214, d97449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96215 q = 0) : d97450 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d96215, d97450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96215, d97450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d96216 q = 0) : d97451 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d96216, d97451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96216, d97451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96217 q = 0) : d97452 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d96217, d97452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96217, d97452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96218 q = 0) : d97453 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d96218, d97453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96218, d97453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96219 q = 0) : d97454 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d96219, d97454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96219, d97454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6345 (p : Pattern) (selected : d174 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d172 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d173 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d174 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6346 (p : Pattern) (selected : d94862 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d94858 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d94858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6345 q selected
    | true =>
      simp only [d94858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d94859 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d94859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d94860 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d94860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d94861 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d94861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d94861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d94862 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d94862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d94862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6347 (p : Pattern) (selected : d94868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d94863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d94863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6346 q selected
    | true =>
      simp only [d94863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d94864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d94864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d94865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d94865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d94866 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d94866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d94867 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d94867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d94868 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6348 (p : Pattern) (selected : d94874 p = 1) : d98500 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d94839 q = 1) : d94839 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d94845 q = 1) : d94845 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d94857 q = 1) : d94857 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d94869 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6347 q selected
    | true =>
      simp only [d94869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d94870 q = 1) : d98496 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94870, d98496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d94870, d98496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d94769 q = 1) : d94769 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d94871 q = 1) : d98497 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94871, d98497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d94871, d98497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d94872 q = 1) : d98498 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94872, d98498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d94872, d98498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d94873 q = 1) : d98499 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94873, d98499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d94873, d98499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d94874 q = 1) : d98500 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94874, d98500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94874, d98500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro6349 (p : Pattern) (selected : d94886 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d94863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d94863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6346 q selected
    | true =>
      simp only [d94863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d94864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d94864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d94865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d94865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d94866 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d94866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d94867 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d94867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d94886 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d94886, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6350 (p : Pattern) (selected : d94892 p = 1) : d98505 p = 1 := by
  have h0 (q : Pattern) (selected : d94839 q = 1) : d94839 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d94845 q = 1) : d94845 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d94857 q = 1) : d94857 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d94869 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6347 q selected
    | true =>
      simp only [d94869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d94870 q = 1) : d98496 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94870, d98496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d94870, d98496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d94769 q = 1) : d94769 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d94871 q = 1) : d98497 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94871, d98497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d94871, d98497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d94872 q = 1) : d98498 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94872, d98498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d94872, d98498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d94873 q = 1) : d98499 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94873, d98499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94873, d98499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d94879 q = 1) : d94879 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d94883 q = 1) : d94883 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d94885 q = 1) : d94885 q = 1 := by
    exact selected
  have h13 (q : Pattern) (selected : d94887 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6349 q selected
    | true =>
      simp only [d94887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h14 (q : Pattern) (selected : d94888 q = 1) : d98501 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94888, d98501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d94888, d98501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d94776 q = 1) : d94776 q = 1 := by
    exact selected
  have h16 (q : Pattern) (selected : d94889 q = 1) : d98502 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94889, d98502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d94889, d98502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d94890 q = 1) : d98503 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94890, d98503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d94890, d98503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d94891 q = 1) : d98504 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94891, d98504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d94891, d98504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d94892 q = 1) : d98505 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94892, d98505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d94892, d98505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro6351 (p : Pattern) (selected : d94901 p = 1) : d98512 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d94885 q = 1) : d94885 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d94887 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6349 q selected
    | true =>
      simp only [d94887, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d94888 q = 1) : d98501 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94888, d98501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d94888, d98501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d94776 q = 1) : d94776 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d94889 q = 1) : d98502 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94889, d98502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d94889, d98502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d94899 q = 1) : d98510 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94899, d98510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94899, d98510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d94900 q = 1) : d98511 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94900, d98511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94900, d98511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d94901 q = 1) : d98512 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94901, d98512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94901, d98512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6352 (p : Pattern) (selected : d249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
  have h2 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d248 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d249 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro6353 (p : Pattern) (selected : d94923 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d94919 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d94919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6352 q selected
    | true =>
      simp only [d94919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d94920 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d94920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d94921 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d94921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d94922 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d94922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d94922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d94923 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d94923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d94923, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6354 (p : Pattern) (selected : d94929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d94924 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d94924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6353 q selected
    | true =>
      simp only [d94924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d94925 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d94925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d94926 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d94926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d94926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d94927 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d94927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d94927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d94928 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d94928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d94928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d94929 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d94929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d94929, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6355 (p : Pattern) (selected : d94935 p = 1) : d98522 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d94918 q = 1) : d94918 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d94930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d94930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6354 q selected
    | true =>
      simp only [d94930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d94931 q = 1) : d98518 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d94931, d98518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d94931, d98518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d94803 q = 1) : d94803 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d94932 q = 1) : d98519 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d94932, d98519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d94932, d98519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d94933 q = 1) : d98520 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d94933, d98520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94933, d98520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d94934 q = 1) : d98521 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d94934, d98521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94934, d98521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d94935 q = 1) : d98522 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d94935, d98522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94935, d98522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6356 (p : Pattern) (selected : d94941 p = 1) : d98528 p = 1 := by
  have h0 (q : Pattern) (selected : d94833 q = 1) : d94833 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d94893 q = 1) : d98506 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94893, d98506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6348 q selected
    | true =>
      simp only [d94893, d98506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6350 q selected
  have h2 (q : Pattern) (selected : d94895 q = 1) : d94895 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d94896 q = 1) : d98507 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94896, d98507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d94896, d98507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d94897 q = 1) : d98508 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94897, d98508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d94897, d98508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d94898 q = 1) : d98509 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94898, d98509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94898, d98509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d94902 q = 1) : d98513 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94902, d98513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d94902, d98513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6351 q selected
  have h8 (q : Pattern) (selected : d94903 q = 1) : d98514 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94903, d98514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d94903, d98514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h9 (q : Pattern) (selected : d94904 q = 1) : d98515 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94904, d98515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d94904, d98515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h10 (q : Pattern) (selected : d94905 q = 1) : d98516 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94905, d98516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d94905, d98516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d94906 q = 1) : d98517 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94906, d98517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d94906, d98517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d94936 q = 1) : d98523 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d94936, d98523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d94936, d98523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6355 q selected
  have h13 (q : Pattern) (selected : d94937 q = 1) : d98524 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d94937, d98524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d94937, d98524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h14 (q : Pattern) (selected : d94938 q = 1) : d98525 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d94938, d98525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d94938, d98525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h15 (q : Pattern) (selected : d94939 q = 1) : d98526 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d94939, d98526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d94939, d98526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h16 (q : Pattern) (selected : d94940 q = 1) : d98527 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d94940, d98527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d94940, d98527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d94941 q = 1) : d98528 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d94941, d98528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d94941, d98528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro6357 (p : Pattern) (selected : d94947 p = 1) : d98534 p = 1 := by
  have h0 (q : Pattern) (selected : d94818 q = 1) : d94818 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d94942 q = 1) : d98529 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d94942, d98529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d94942, d98529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6356 q selected
  have h3 (q : Pattern) (selected : d94943 q = 1) : d98530 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d94943, d98530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d94943, d98530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d94944 q = 1) : d98531 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d94944, d98531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d94944, d98531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d94945 q = 1) : d98532 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d94945, d98532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d94945, d98532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d94946 q = 1) : d98533 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d94946, d98533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d94946, d98533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d94947 q = 1) : d98534 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d94947, d98534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94947, d98534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro6358 (p : Pattern) (selected : d354 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d350 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
    | true =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d351 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d352 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d353 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d172 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d173 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d354 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro6359 (p : Pattern) (selected : d94999 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d94995 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d94995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6358 q selected
    | true =>
      simp only [d94995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6345 q selected
  have h2 (q : Pattern) (selected : d94996 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d94996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d94997 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d94997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d94858 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d94858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6345 q selected
    | true =>
      simp only [d94858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d94859 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d94859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d94860 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d94860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d94998 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d94998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d94998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d94999 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d94999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d94999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6360 (p : Pattern) (selected : d95005 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95000 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6359 q selected
    | true =>
      simp only [d95000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95001 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d94863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d94863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6346 q selected
    | true =>
      simp only [d94863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d94864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d94864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95002 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95003 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95004 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95005 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6361 (p : Pattern) (selected : d95017 p = 1) : d98539 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d94968 q = 1) : d94968 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d94974 q = 1) : d94974 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d94994 q = 1) : d94994 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d95006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6360 q selected
    | true =>
      simp only [d95006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6347 q selected
  have h5 (q : Pattern) (selected : d95007 q = 1) : d98535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95007, d98535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95007, d98535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95013 q = 1) : d95013 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d95014 q = 1) : d98536 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95014, d98536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95014, d98536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95015 q = 1) : d98537 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95015, d98537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95015, d98537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d95016 q = 1) : d98538 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95016, d98538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95016, d98538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d95017 q = 1) : d98539 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d95017, d98539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95017, d98539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro6362 (p : Pattern) (selected : d95030 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95000 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6359 q selected
    | true =>
      simp only [d95000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95001 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d94863 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d94863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6346 q selected
    | true =>
      simp only [d94863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d94864 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d94864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95002 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95003 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95004 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95030 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6363 (p : Pattern) (selected : d95039 p = 1) : d98544 p = 1 := by
  have h0 (q : Pattern) (selected : d94968 q = 1) : d94968 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d94974 q = 1) : d94974 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d94994 q = 1) : d94994 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d95006 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6360 q selected
    | true =>
      simp only [d95006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6347 q selected
  have h4 (q : Pattern) (selected : d95007 q = 1) : d98535 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95007, d98535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95007, d98535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95013 q = 1) : d95013 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d95014 q = 1) : d98536 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95014, d98536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95014, d98536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95015 q = 1) : d98537 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95015, d98537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95015, d98537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95016 q = 1) : d98538 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95016, d98538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95016, d98538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d95022 q = 1) : d95022 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d95026 q = 1) : d95026 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d95029 q = 1) : d95029 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d95031 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6362 q selected
    | true =>
      simp only [d95031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6349 q selected
  have h13 (q : Pattern) (selected : d95032 q = 1) : d98540 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95032, d98540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d95032, d98540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d95035 q = 1) : d95035 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d95036 q = 1) : d98541 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95036, d98541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d95036, d98541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d95037 q = 1) : d98542 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95037, d98542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d95037, d98542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d95038 q = 1) : d98543 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95038, d98543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d95038, d98543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d95039 q = 1) : d98544 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d95039, d98544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d95039, d98544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro6364 (p : Pattern) (selected : d95053 p = 1) : d98551 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95029 q = 1) : d95029 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d95031 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6362 q selected
    | true =>
      simp only [d95031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6349 q selected
  have h3 (q : Pattern) (selected : d95032 q = 1) : d98540 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95032, d98540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95032, d98540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95035 q = 1) : d95035 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d95036 q = 1) : d98541 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95036, d98541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95036, d98541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95051 q = 1) : d98549 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95051, d98549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95051, d98549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95052 q = 1) : d98550 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95052, d98550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95052, d98550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95053 q = 1) : d98551 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d95053, d98551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95053, d98551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6365 (p : Pattern) (selected : d435 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d431 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
  have h2 (q : Pattern) (selected : d350 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro15 q selected
    | true =>
      simp only [d350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d432 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d351 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d433 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d434 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d245 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
  have h8 (q : Pattern) (selected : d170 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1 q selected
    | true =>
      simp only [d170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d246 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d171 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d247 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d248 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d435 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro6366 (p : Pattern) (selected : d95085 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95081 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6365 q selected
    | true =>
      simp only [d95081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6352 q selected
  have h2 (q : Pattern) (selected : d95082 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95083 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d94919 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d94919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6352 q selected
    | true =>
      simp only [d94919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d94920 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d94920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d94921 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d94921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95084 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95085 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6367 (p : Pattern) (selected : d95091 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95086 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6366 q selected
    | true =>
      simp only [d95086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95087 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d94924 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d94924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6353 q selected
    | true =>
      simp only [d94924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d94925 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d94925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d94925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95088 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95089 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95090 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95091 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6368 (p : Pattern) (selected : d95103 p = 1) : d98561 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95080 q = 1) : d95080 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d95092 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6367 q selected
    | true =>
      simp only [d95092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6354 q selected
  have h3 (q : Pattern) (selected : d95093 q = 1) : d98557 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95093, d98557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95093, d98557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95099 q = 1) : d95099 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d95100 q = 1) : d98558 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95100, d98558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95100, d98558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95101 q = 1) : d98559 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95101, d98559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95101, d98559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95102 q = 1) : d98560 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95102, d98560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95102, d98560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95103 q = 1) : d98561 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d95103, d98561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95103, d98561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6369 (p : Pattern) (selected : d95115 p = 1) : d98567 p = 1 := by
  have h0 (q : Pattern) (selected : d94962 q = 1) : d94962 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95040 q = 1) : d98545 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95040, d98545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6361 q selected
    | true =>
      simp only [d95040, d98545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6363 q selected
  have h2 (q : Pattern) (selected : d95047 q = 1) : d95047 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d95048 q = 1) : d98546 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d95048, d98546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95048, d98546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d95049 q = 1) : d98547 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d95049, d98547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95049, d98547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95050 q = 1) : d98548 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d95050, d98548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95050, d98548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95054 q = 1) : d98552 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95054, d98552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95054, d98552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6364 q selected
  have h8 (q : Pattern) (selected : d95056 q = 1) : d95056 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d95057 q = 1) : d98553 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d95057, d98553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95057, d98553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d95058 q = 1) : d98554 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d95058, d98554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d95058, d98554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d95059 q = 1) : d98555 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d95059, d98555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d95059, d98555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d95060 q = 1) : d98556 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d95060, d98556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95060, d98556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d95104 q = 1) : d98562 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95104, d98562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95104, d98562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6368 q selected
  have h14 (q : Pattern) (selected : d95110 q = 1) : d95110 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d95111 q = 1) : d98563 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d95111, d98563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d95111, d98563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d95112 q = 1) : d98564 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d95112, d98564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d95112, d98564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d95113 q = 1) : d98565 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d95113, d98565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d95113, d98565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d95114 q = 1) : d98566 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d95114, d98566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d95114, d98566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d95115 q = 1) : d98567 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95115, d98567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d95115, d98567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro6370 (p : Pattern) (selected : d95121 p = 1) : d98573 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95116 q = 1) : d98568 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d95116, d98568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95116, d98568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6369 q selected
  have h2 (q : Pattern) (selected : d95117 q = 1) : d98569 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d95117, d98569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95117, d98569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95118 q = 1) : d98570 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d95118, d98570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95118, d98570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95119 q = 1) : d98571 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d95119, d98571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95119, d98571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95120 q = 1) : d98572 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d95120, d98572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95120, d98572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95121 q = 1) : d98573 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d95121, d98573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95121, d98573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6371 (p : Pattern) (selected : d878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d574 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30 q selected
    | true =>
      simp only [d574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d575 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d576 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d577 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d875 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d876 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d877 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d878 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d878, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro6372 (p : Pattern) (selected : d880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d875 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d876 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d876, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d877 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d877, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d880 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d880, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6373 (p : Pattern) (selected : d95208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95201 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6371 q selected
    | true =>
      simp only [d95201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6372 q selected
  have h2 (q : Pattern) (selected : d95202 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95203 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6372 q selected
    | true =>
      simp only [d95204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95207 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95208 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6374 (p : Pattern) (selected : d95212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95204 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6372 q selected
    | true =>
      simp only [d95204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95205 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95206 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95211 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95212 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6375 (p : Pattern) (selected : d95218 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95209 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6373 q selected
    | true =>
      simp only [d95209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95210 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95213 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6374 q selected
    | true =>
      simp only [d95213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95214 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95215 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95216 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95217 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95218 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6376 (p : Pattern) (selected : d95222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95213 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6374 q selected
    | true =>
      simp only [d95213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95214 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95219 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95220 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95221 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d95222 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6377 (p : Pattern) (selected : d95234 p = 1) : d98579 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95171 q = 1) : d95171 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d95180 q = 1) : d95180 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d95200 q = 1) : d95200 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d95223 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6375 q selected
    | true =>
      simp only [d95223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6376 q selected
  have h5 (q : Pattern) (selected : d95224 q = 1) : d98575 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95224, d98575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95224, d98575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95230 q = 1) : d95230 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d95231 q = 1) : d98576 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95231, d98576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95231, d98576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95232 q = 1) : d98577 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95232, d98577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95232, d98577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d95233 q = 1) : d98578 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95233, d98578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95233, d98578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d95234 q = 1) : d98579 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d95234, d98579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95234, d98579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro6378 (p : Pattern) (selected : d95249 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95209 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6373 q selected
    | true =>
      simp only [d95209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95210 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95213 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6374 q selected
    | true =>
      simp only [d95213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95214 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95215 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95216 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95217 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95249 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6379 (p : Pattern) (selected : d95250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95213 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6374 q selected
    | true =>
      simp only [d95213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95214 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95219 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95220 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95221 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d95250 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6380 (p : Pattern) (selected : d95259 p = 1) : d98584 p = 1 := by
  have h0 (q : Pattern) (selected : d95171 q = 1) : d95171 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95180 q = 1) : d95180 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d95200 q = 1) : d95200 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d95223 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6375 q selected
    | true =>
      simp only [d95223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6376 q selected
  have h4 (q : Pattern) (selected : d95224 q = 1) : d98575 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95224, d98575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95224, d98575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95230 q = 1) : d95230 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d95231 q = 1) : d98576 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95231, d98576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95231, d98576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95232 q = 1) : d98577 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95232, d98577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95232, d98577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95233 q = 1) : d98578 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95233, d98578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95233, d98578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d95240 q = 1) : d95240 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d95245 q = 1) : d95245 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d95248 q = 1) : d95248 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d95251 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6378 q selected
    | true =>
      simp only [d95251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6379 q selected
  have h13 (q : Pattern) (selected : d95252 q = 1) : d98580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95252, d98580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d95252, d98580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d95255 q = 1) : d95255 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d95256 q = 1) : d98581 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95256, d98581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d95256, d98581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d95257 q = 1) : d98582 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95257, d98582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d95257, d98582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d95258 q = 1) : d98583 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95258, d98583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d95258, d98583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d95259 q = 1) : d98584 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d95259, d98584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d95259, d98584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro6381 (p : Pattern) (selected : d95284 p = 1) : d98591 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95248 q = 1) : d95248 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d95251 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6378 q selected
    | true =>
      simp only [d95251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6379 q selected
  have h3 (q : Pattern) (selected : d95252 q = 1) : d98580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95252, d98580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95252, d98580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95255 q = 1) : d95255 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d95256 q = 1) : d98581 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95256, d98581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95256, d98581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95282 q = 1) : d98589 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95282, d98589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95282, d98589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95283 q = 1) : d98590 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95283, d98590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95283, d98590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95284 q = 1) : d98591 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d95284, d98591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95284, d98591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6382 (p : Pattern) (selected : d1022 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d691 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30 q selected
  have h2 (q : Pattern) (selected : d574 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30 q selected
    | true =>
      simp only [d574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d692 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d575 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d693 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d694 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1018 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
  have h8 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1019 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d875 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d1020 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1021 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d1022 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro6383 (p : Pattern) (selected : d1024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1018 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
  have h2 (q : Pattern) (selected : d874 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro52 q selected
    | true =>
      simp only [d874, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1019 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d875 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d875, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1020 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1021 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1024 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro6384 (p : Pattern) (selected : d95329 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95322 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6382 q selected
    | true =>
      simp only [d95322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6383 q selected
  have h2 (q : Pattern) (selected : d95323 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95324 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95325 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6383 q selected
    | true =>
      simp only [d95325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95326 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95327 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95328 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95329 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6385 (p : Pattern) (selected : d95333 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95325 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6383 q selected
    | true =>
      simp only [d95325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95326 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95327 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95332 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95333 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6386 (p : Pattern) (selected : d95339 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95330 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6384 q selected
    | true =>
      simp only [d95330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95331 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95334 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6385 q selected
    | true =>
      simp only [d95334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95335 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95336 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95337 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95338 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95339 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6387 (p : Pattern) (selected : d95343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95334 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6385 q selected
    | true =>
      simp only [d95334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95335 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95340 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95341 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95342 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d95343 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6388 (p : Pattern) (selected : d95359 p = 1) : d98601 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95321 q = 1) : d95321 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d95344 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6386 q selected
    | true =>
      simp only [d95344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6387 q selected
  have h3 (q : Pattern) (selected : d95345 q = 1) : d98597 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95345, d98597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95345, d98597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95355 q = 1) : d95355 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d95356 q = 1) : d98598 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95356, d98598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95356, d98598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95357 q = 1) : d98599 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95357, d98599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95357, d98599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95358 q = 1) : d98600 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95358, d98600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95358, d98600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95359 q = 1) : d98601 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d95359, d98601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95359, d98601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6389 (p : Pattern) (selected : d95376 p = 1) : d98607 p = 1 := by
  have h0 (q : Pattern) (selected : d95163 q = 1) : d95163 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95260 q = 1) : d98585 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95260, d98585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6377 q selected
    | true =>
      simp only [d95260, d98585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6380 q selected
  have h2 (q : Pattern) (selected : d95278 q = 1) : d95278 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d95279 q = 1) : d98586 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d95279, d98586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95279, d98586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d95280 q = 1) : d98587 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d95280, d98587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95280, d98587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95281 q = 1) : d98588 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d95281, d98588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95281, d98588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95285 q = 1) : d98592 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95285, d98592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95285, d98592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6381 q selected
  have h8 (q : Pattern) (selected : d95287 q = 1) : d95287 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d95288 q = 1) : d98593 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d95288, d98593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95288, d98593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d95289 q = 1) : d98594 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d95289, d98594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d95289, d98594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d95290 q = 1) : d98595 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d95290, d98595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d95290, d98595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d95291 q = 1) : d98596 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d95291, d98596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95291, d98596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d95360 q = 1) : d98602 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95360, d98602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95360, d98602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6388 q selected
  have h14 (q : Pattern) (selected : d95371 q = 1) : d95371 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d95372 q = 1) : d98603 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d95372, d98603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d95372, d98603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d95373 q = 1) : d98604 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d95373, d98604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d95373, d98604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d95374 q = 1) : d98605 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d95374, d98605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d95374, d98605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d95375 q = 1) : d98606 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d95375, d98606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d95375, d98606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d95376 q = 1) : d98607 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95376, d98607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d95376, d98607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro6390 (p : Pattern) (selected : d95382 p = 1) : d98613 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95377 q = 1) : d98608 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d95377, d98608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95377, d98608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6389 q selected
  have h2 (q : Pattern) (selected : d95378 q = 1) : d98609 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d95378, d98609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95378, d98609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95379 q = 1) : d98610 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d95379, d98610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95379, d98610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95380 q = 1) : d98611 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d95380, d98611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95380, d98611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95381 q = 1) : d98612 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d95381, d98612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95381, d98612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95382 q = 1) : d98613 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d95382, d98613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95382, d98613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6391 (p : Pattern) (selected : d1280 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1265 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro80 q selected
    | true =>
      simp only [d1265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1266 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1267 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1268 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1276 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
    | true =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1277 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1278 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1279 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1280 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro6392 (p : Pattern) (selected : d1282 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1276 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
    | true =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1277 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1278 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1279 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1282 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6393 (p : Pattern) (selected : d1295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1291 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro84 q selected
    | true =>
      simp only [d1291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1292 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1293 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1294 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1295 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6394 (p : Pattern) (selected : d95470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95463 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6391 q selected
    | true =>
      simp only [d95463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6392 q selected
  have h2 (q : Pattern) (selected : d95464 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95465 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95466 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6392 q selected
    | true =>
      simp only [d95466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6393 q selected
  have h5 (q : Pattern) (selected : d95467 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95468 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95469 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95470 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6395 (p : Pattern) (selected : d95474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95466 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6392 q selected
    | true =>
      simp only [d95466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6393 q selected
  have h2 (q : Pattern) (selected : d95467 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95468 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95473 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95474 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6396 (p : Pattern) (selected : d95480 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6394 q selected
    | true =>
      simp only [d95471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95475 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6395 q selected
    | true =>
      simp only [d95475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95476 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95477 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95478 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95479 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95480 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6397 (p : Pattern) (selected : d95484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95475 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6395 q selected
    | true =>
      simp only [d95475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95476 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95481 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95482 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95483 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d95484 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6398 (p : Pattern) (selected : d95496 p = 1) : d98620 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95433 q = 1) : d95433 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d95442 q = 1) : d95442 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d95462 q = 1) : d95462 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d95485 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6396 q selected
    | true =>
      simp only [d95485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6397 q selected
  have h5 (q : Pattern) (selected : d95486 q = 1) : d98616 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95486, d98616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95486, d98616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95492 q = 1) : d95492 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d95493 q = 1) : d98617 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95493, d98617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95493, d98617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95494 q = 1) : d98618 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95494, d98618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95494, d98618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d95495 q = 1) : d98619 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95495, d98619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95495, d98619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d95496 q = 1) : d98620 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d95496, d98620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95496, d98620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro6399 (p : Pattern) (selected : d95511 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95471 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6394 q selected
    | true =>
      simp only [d95471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95472 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95475 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6395 q selected
    | true =>
      simp only [d95475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95476 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95477 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95478 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95479 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95511 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6400 (p : Pattern) (selected : d95512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95475 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6395 q selected
    | true =>
      simp only [d95475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95476 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95481 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95482 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95483 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d95512 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6401 (p : Pattern) (selected : d95521 p = 1) : d98625 p = 1 := by
  have h0 (q : Pattern) (selected : d95433 q = 1) : d95433 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95442 q = 1) : d95442 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d95462 q = 1) : d95462 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d95485 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6396 q selected
    | true =>
      simp only [d95485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6397 q selected
  have h4 (q : Pattern) (selected : d95486 q = 1) : d98616 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95486, d98616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95486, d98616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95492 q = 1) : d95492 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d95493 q = 1) : d98617 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95493, d98617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95493, d98617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95494 q = 1) : d98618 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95494, d98618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95494, d98618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95495 q = 1) : d98619 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95495, d98619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95495, d98619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d95502 q = 1) : d95502 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d95507 q = 1) : d95507 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d95510 q = 1) : d95510 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d95513 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6399 q selected
    | true =>
      simp only [d95513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6400 q selected
  have h13 (q : Pattern) (selected : d95514 q = 1) : d98621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95514, d98621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d95514, d98621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d95517 q = 1) : d95517 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d95518 q = 1) : d98622 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95518, d98622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d95518, d98622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d95519 q = 1) : d98623 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95519, d98623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d95519, d98623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d95520 q = 1) : d98624 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95520, d98624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d95520, d98624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d95521 q = 1) : d98625 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d95521, d98625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d95521, d98625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro6402 (p : Pattern) (selected : d95546 p = 1) : d98632 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95510 q = 1) : d95510 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d95513 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6399 q selected
    | true =>
      simp only [d95513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6400 q selected
  have h3 (q : Pattern) (selected : d95514 q = 1) : d98621 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95514, d98621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95514, d98621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95517 q = 1) : d95517 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d95518 q = 1) : d98622 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95518, d98622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95518, d98622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95544 q = 1) : d98630 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95544, d98630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95544, d98630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95545 q = 1) : d98631 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95545, d98631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95545, d98631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95546 q = 1) : d98632 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d95546, d98632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95546, d98632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6403 (p : Pattern) (selected : d1451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1442 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro80 q selected
  have h2 (q : Pattern) (selected : d1265 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro80 q selected
    | true =>
      simp only [d1265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1443 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1266 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1444 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1445 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1447 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
  have h8 (q : Pattern) (selected : d1276 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
    | true =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1448 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1277 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d1449 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1450 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d1451 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro6404 (p : Pattern) (selected : d1453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1447 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
  have h2 (q : Pattern) (selected : d1276 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro81 q selected
    | true =>
      simp only [d1276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1448 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1277 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1449 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1450 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1453 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro6405 (p : Pattern) (selected : d1462 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1458 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro84 q selected
  have h2 (q : Pattern) (selected : d1291 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro84 q selected
    | true =>
      simp only [d1291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1459 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1292 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1460 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1461 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1462 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro6406 (p : Pattern) (selected : d95591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95584 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6403 q selected
    | true =>
      simp only [d95584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6404 q selected
  have h2 (q : Pattern) (selected : d95585 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95586 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95587 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6404 q selected
    | true =>
      simp only [d95587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6405 q selected
  have h5 (q : Pattern) (selected : d95588 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95589 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95590 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95591 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6407 (p : Pattern) (selected : d95595 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95587 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6404 q selected
    | true =>
      simp only [d95587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6405 q selected
  have h2 (q : Pattern) (selected : d95588 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95589 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95594 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95595 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6408 (p : Pattern) (selected : d95601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95592 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6406 q selected
    | true =>
      simp only [d95592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95593 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95596 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6407 q selected
    | true =>
      simp only [d95596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95597 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95598 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95599 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95600 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95601 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6409 (p : Pattern) (selected : d95605 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95596 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6407 q selected
    | true =>
      simp only [d95596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95597 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95602 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95603 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95604 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d95605 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6410 (p : Pattern) (selected : d95621 p = 1) : d98642 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95583 q = 1) : d95583 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d95606 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6408 q selected
    | true =>
      simp only [d95606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6409 q selected
  have h3 (q : Pattern) (selected : d95607 q = 1) : d98638 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95607, d98638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95607, d98638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95617 q = 1) : d95617 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d95618 q = 1) : d98639 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95618, d98639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95618, d98639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95619 q = 1) : d98640 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95619, d98640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95619, d98640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95620 q = 1) : d98641 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95620, d98641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95620, d98641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95621 q = 1) : d98642 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d95621, d98642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95621, d98642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6411 (p : Pattern) (selected : d95638 p = 1) : d98648 p = 1 := by
  have h0 (q : Pattern) (selected : d95425 q = 1) : d95425 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95522 q = 1) : d98626 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95522, d98626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6398 q selected
    | true =>
      simp only [d95522, d98626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6401 q selected
  have h2 (q : Pattern) (selected : d95540 q = 1) : d95540 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d95541 q = 1) : d98627 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d95541, d98627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95541, d98627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d95542 q = 1) : d98628 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d95542, d98628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95542, d98628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95543 q = 1) : d98629 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d95543, d98629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95543, d98629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95547 q = 1) : d98633 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95547, d98633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95547, d98633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6402 q selected
  have h8 (q : Pattern) (selected : d95549 q = 1) : d95549 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d95550 q = 1) : d98634 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d95550, d98634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95550, d98634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d95551 q = 1) : d98635 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d95551, d98635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d95551, d98635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d95552 q = 1) : d98636 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d95552, d98636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d95552, d98636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d95553 q = 1) : d98637 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d95553, d98637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95553, d98637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d95622 q = 1) : d98643 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95622, d98643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95622, d98643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6410 q selected
  have h14 (q : Pattern) (selected : d95633 q = 1) : d95633 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d95634 q = 1) : d98644 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d95634, d98644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d95634, d98644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d95635 q = 1) : d98645 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d95635, d98645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d95635, d98645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d95636 q = 1) : d98646 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d95636, d98646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d95636, d98646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d95637 q = 1) : d98647 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d95637, d98647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d95637, d98647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d95638 q = 1) : d98648 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95638, d98648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d95638, d98648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro6412 (p : Pattern) (selected : d95644 p = 1) : d98654 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95639 q = 1) : d98649 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d95639, d98649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95639, d98649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6411 q selected
  have h2 (q : Pattern) (selected : d95640 q = 1) : d98650 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d95640, d98650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95640, d98650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95641 q = 1) : d98651 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d95641, d98651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95641, d98651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95642 q = 1) : d98652 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d95642, d98652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95642, d98652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95643 q = 1) : d98653 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d95643, d98653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95643, d98653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95644 q = 1) : d98654 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d95644, d98654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95644, d98654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6413 (p : Pattern) (selected : d1757 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1741 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro116 q selected
    | true =>
      simp only [d1741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1742 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1743 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1744 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1753 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro117 q selected
    | true =>
      simp only [d1753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1754 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1755 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d1756 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1757 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro6414 (p : Pattern) (selected : d1759 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1753 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro117 q selected
    | true =>
      simp only [d1753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1754 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1755 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1756 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1759 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6415 (p : Pattern) (selected : d1772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1768 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro120 q selected
    | true =>
      simp only [d1768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d1769 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1770 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1771 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1772 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6416 (p : Pattern) (selected : d95733 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95726 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6413 q selected
    | true =>
      simp only [d95726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6414 q selected
  have h2 (q : Pattern) (selected : d95727 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95728 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95729 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6414 q selected
    | true =>
      simp only [d95729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6415 q selected
  have h5 (q : Pattern) (selected : d95730 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95731 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95732 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95733 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6417 (p : Pattern) (selected : d95737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95729 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6414 q selected
    | true =>
      simp only [d95729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6415 q selected
  have h2 (q : Pattern) (selected : d95730 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95731 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95736 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95737 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6418 (p : Pattern) (selected : d95743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6416 q selected
    | true =>
      simp only [d95734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95738 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6417 q selected
    | true =>
      simp only [d95738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95739 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95741 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95742 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95743 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6419 (p : Pattern) (selected : d95747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95738 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6417 q selected
    | true =>
      simp only [d95738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95739 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95744 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95745 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95746 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d95747 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6420 (p : Pattern) (selected : d95759 p = 1) : d98662 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95696 q = 1) : d95696 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d95705 q = 1) : d95705 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d95725 q = 1) : d95725 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d95748 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6418 q selected
    | true =>
      simp only [d95748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6419 q selected
  have h5 (q : Pattern) (selected : d95749 q = 1) : d98658 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95749, d98658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95749, d98658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95755 q = 1) : d95755 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d95756 q = 1) : d98659 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95756, d98659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95756, d98659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95757 q = 1) : d98660 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95757, d98660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95757, d98660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d95758 q = 1) : d98661 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95758, d98661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95758, d98661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d95759 q = 1) : d98662 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d95759, d98662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95759, d98662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro6421 (p : Pattern) (selected : d95774 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95734 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6416 q selected
    | true =>
      simp only [d95734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95735 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95738 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6417 q selected
    | true =>
      simp only [d95738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95739 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95740 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95741 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95742 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95774 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6422 (p : Pattern) (selected : d95775 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95738 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6417 q selected
    | true =>
      simp only [d95738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95739 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95744 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95745 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95746 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d95775 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6423 (p : Pattern) (selected : d95784 p = 1) : d98667 p = 1 := by
  have h0 (q : Pattern) (selected : d95696 q = 1) : d95696 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95705 q = 1) : d95705 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d95725 q = 1) : d95725 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d95748 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6418 q selected
    | true =>
      simp only [d95748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6419 q selected
  have h4 (q : Pattern) (selected : d95749 q = 1) : d98658 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95749, d98658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95749, d98658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95755 q = 1) : d95755 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d95756 q = 1) : d98659 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95756, d98659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95756, d98659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95757 q = 1) : d98660 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95757, d98660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95757, d98660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95758 q = 1) : d98661 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95758, d98661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95758, d98661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d95765 q = 1) : d95765 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d95770 q = 1) : d95770 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d95773 q = 1) : d95773 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d95776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6421 q selected
    | true =>
      simp only [d95776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6422 q selected
  have h13 (q : Pattern) (selected : d95777 q = 1) : d98663 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95777, d98663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d95777, d98663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d95780 q = 1) : d95780 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d95781 q = 1) : d98664 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95781, d98664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d95781, d98664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d95782 q = 1) : d98665 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95782, d98665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d95782, d98665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d95783 q = 1) : d98666 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95783, d98666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d95783, d98666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d95784 q = 1) : d98667 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d95784, d98667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d95784, d98667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro6424 (p : Pattern) (selected : d95809 p = 1) : d98674 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95773 q = 1) : d95773 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d95776 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6421 q selected
    | true =>
      simp only [d95776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6422 q selected
  have h3 (q : Pattern) (selected : d95777 q = 1) : d98663 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95777, d98663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95777, d98663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95780 q = 1) : d95780 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d95781 q = 1) : d98664 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95781, d98664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95781, d98664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95807 q = 1) : d98672 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95807, d98672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95807, d98672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95808 q = 1) : d98673 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95808, d98673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95808, d98673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95809 q = 1) : d98674 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d95809, d98674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95809, d98674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6425 (p : Pattern) (selected : d1928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1919 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1919, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro116 q selected
  have h2 (q : Pattern) (selected : d1741 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro116 q selected
    | true =>
      simp only [d1741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1920 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1920, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1742 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1921 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1922 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1924 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro117 q selected
  have h8 (q : Pattern) (selected : d1753 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro117 q selected
    | true =>
      simp only [d1753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d1925 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d1925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1754 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d1926 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d1926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d1927 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d1928 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1928, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro6426 (p : Pattern) (selected : d1930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1924 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1924, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro117 q selected
  have h2 (q : Pattern) (selected : d1753 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro117 q selected
    | true =>
      simp only [d1753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1925 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1925, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1754 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1926 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1926, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1927 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1927, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1930 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1930, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro6427 (p : Pattern) (selected : d1939 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1935 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1935, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro120 q selected
  have h2 (q : Pattern) (selected : d1768 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d1768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro120 q selected
    | true =>
      simp only [d1768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1936 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1936, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1769 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d1769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1937 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d1937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1937, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1938 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d1938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d1939 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d1939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1939, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro6428 (p : Pattern) (selected : d95854 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95847 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6425 q selected
    | true =>
      simp only [d95847, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6426 q selected
  have h2 (q : Pattern) (selected : d95848 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95849 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95850 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6426 q selected
    | true =>
      simp only [d95850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6427 q selected
  have h5 (q : Pattern) (selected : d95851 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95852 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95853 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95853, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95854 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95854, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6429 (p : Pattern) (selected : d95858 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95850 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6426 q selected
    | true =>
      simp only [d95850, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6427 q selected
  have h2 (q : Pattern) (selected : d95851 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95851, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95852 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95852, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95857 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95858 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95858, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6430 (p : Pattern) (selected : d95864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95855 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6428 q selected
    | true =>
      simp only [d95855, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95856 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95856, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6429 q selected
    | true =>
      simp only [d95859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95861 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95862 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d95863 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95863, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d95864 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95864, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6431 (p : Pattern) (selected : d95868 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95859 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6429 q selected
    | true =>
      simp only [d95859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95860 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95865 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d95865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d95865, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d95866 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d95866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95866, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d95867 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d95867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95867, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d95868 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d95868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d95868, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6432 (p : Pattern) (selected : d95884 p = 1) : d98684 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95846 q = 1) : d95846 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d95869 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d95869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6430 q selected
    | true =>
      simp only [d95869, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6431 q selected
  have h3 (q : Pattern) (selected : d95870 q = 1) : d98680 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d95870, d98680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95870, d98680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95880 q = 1) : d95880 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d95881 q = 1) : d98681 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d95881, d98681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95881, d98681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95882 q = 1) : d98682 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d95882, d98682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95882, d98682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95883 q = 1) : d98683 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d95883, d98683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95883, d98683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95884 q = 1) : d98684 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d95884, d98684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95884, d98684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6433 (p : Pattern) (selected : d95901 p = 1) : d98690 p = 1 := by
  have h0 (q : Pattern) (selected : d95688 q = 1) : d95688 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95785 q = 1) : d98668 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95785, d98668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6420 q selected
    | true =>
      simp only [d95785, d98668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6423 q selected
  have h2 (q : Pattern) (selected : d95803 q = 1) : d95803 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d95804 q = 1) : d98669 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d95804, d98669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95804, d98669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d95805 q = 1) : d98670 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d95805, d98670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95805, d98670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95806 q = 1) : d98671 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d95806, d98671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95806, d98671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95810 q = 1) : d98675 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95810, d98675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95810, d98675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6424 q selected
  have h8 (q : Pattern) (selected : d95812 q = 1) : d95812 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d95813 q = 1) : d98676 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d95813, d98676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95813, d98676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d95814 q = 1) : d98677 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d95814, d98677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d95814, d98677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d95815 q = 1) : d98678 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d95815, d98678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d95815, d98678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d95816 q = 1) : d98679 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d95816, d98679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95816, d98679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d95885 q = 1) : d98685 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d95885, d98685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d95885, d98685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6432 q selected
  have h14 (q : Pattern) (selected : d95896 q = 1) : d95896 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d95897 q = 1) : d98686 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d95897, d98686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d95897, d98686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d95898 q = 1) : d98687 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d95898, d98687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d95898, d98687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d95899 q = 1) : d98688 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d95899, d98688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d95899, d98688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d95900 q = 1) : d98689 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d95900, d98689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d95900, d98689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d95901 q = 1) : d98690 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d95901, d98690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d95901, d98690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro6434 (p : Pattern) (selected : d95907 p = 1) : d98696 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95902 q = 1) : d98691 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d95902, d98691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95902, d98691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6433 q selected
  have h2 (q : Pattern) (selected : d95903 q = 1) : d98692 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d95903, d98692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95903, d98692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95904 q = 1) : d98693 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d95904, d98693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95904, d98693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95905 q = 1) : d98694 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d95905, d98694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95905, d98694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d95906 q = 1) : d98695 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d95906, d98695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95906, d98695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95907 q = 1) : d98696 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d95907, d98696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95907, d98696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6435 (p : Pattern) (selected : d2235 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2219 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro153 q selected
    | true =>
      simp only [d2219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2220 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2221 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2222 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2231 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro154 q selected
    | true =>
      simp only [d2231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2232 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2233 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2234 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2235 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro6436 (p : Pattern) (selected : d2237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2231 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro154 q selected
    | true =>
      simp only [d2231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2232 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2233 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2234 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2237 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6437 (p : Pattern) (selected : d2250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2246 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro157 q selected
    | true =>
      simp only [d2246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2247 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2248 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2249 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2250 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6438 (p : Pattern) (selected : d95997 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95990 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6435 q selected
    | true =>
      simp only [d95990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6436 q selected
  have h2 (q : Pattern) (selected : d95991 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95992 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95993 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6436 q selected
    | true =>
      simp only [d95993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6437 q selected
  have h5 (q : Pattern) (selected : d95994 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95995 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95996 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d95996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d95997 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d95997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d95997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6439 (p : Pattern) (selected : d96001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95993 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d95993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6436 q selected
    | true =>
      simp only [d95993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6437 q selected
  have h2 (q : Pattern) (selected : d95994 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d95994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d95995 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d95995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d96000 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96001 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6440 (p : Pattern) (selected : d96007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95998 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6438 q selected
    | true =>
      simp only [d95998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95999 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6439 q selected
    | true =>
      simp only [d96002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d96004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d96006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d96006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d96007 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6441 (p : Pattern) (selected : d96011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d96002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6439 q selected
    | true =>
      simp only [d96002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96008 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96009 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96010 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96011 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6442 (p : Pattern) (selected : d96023 p = 1) : d98705 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95960 q = 1) : d95960 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d95969 q = 1) : d95969 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d95989 q = 1) : d95989 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d96012 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6440 q selected
    | true =>
      simp only [d96012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6441 q selected
  have h5 (q : Pattern) (selected : d96013 q = 1) : d98701 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96013, d98701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96013, d98701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96019 q = 1) : d96019 q = 1 := by
    exact selected
  have h7 (q : Pattern) (selected : d96020 q = 1) : d98702 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96020, d98702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96020, d98702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d96021 q = 1) : d98703 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96021, d98703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96021, d98703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d96022 q = 1) : d98704 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96022, d98704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96022, d98704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d96023 q = 1) : d98705 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96023, d98705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96023, d98705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro6443 (p : Pattern) (selected : d96038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95998 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d95998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6438 q selected
    | true =>
      simp only [d95998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d95999 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d95999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6439 q selected
    | true =>
      simp only [d96002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d96004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d96006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d96006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d96038 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d96038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6444 (p : Pattern) (selected : d96039 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d96002 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6439 q selected
    | true =>
      simp only [d96002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96003 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96008 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96009 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96010 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96039 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6445 (p : Pattern) (selected : d96048 p = 1) : d98710 p = 1 := by
  have h0 (q : Pattern) (selected : d95960 q = 1) : d95960 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d95969 q = 1) : d95969 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d95989 q = 1) : d95989 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d96012 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6440 q selected
    | true =>
      simp only [d96012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6441 q selected
  have h4 (q : Pattern) (selected : d96013 q = 1) : d98701 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96013, d98701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96013, d98701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d96019 q = 1) : d96019 q = 1 := by
    exact selected
  have h6 (q : Pattern) (selected : d96020 q = 1) : d98702 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96020, d98702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96020, d98702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d96021 q = 1) : d98703 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96021, d98703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96021, d98703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d96022 q = 1) : d98704 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96022, d98704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96022, d98704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d96029 q = 1) : d96029 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d96034 q = 1) : d96034 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d96037 q = 1) : d96037 q = 1 := by
    exact selected
  have h12 (q : Pattern) (selected : d96040 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6443 q selected
    | true =>
      simp only [d96040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6444 q selected
  have h13 (q : Pattern) (selected : d96041 q = 1) : d98706 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96041, d98706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d96041, d98706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d96044 q = 1) : d96044 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d96045 q = 1) : d98707 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96045, d98707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d96045, d98707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d96046 q = 1) : d98708 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96046, d98708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d96046, d98708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d96047 q = 1) : d98709 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96047, d98709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d96047, d98709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d96048 q = 1) : d98710 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96048, d98710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d96048, d98710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  exact h18 p selected
theorem eqIntro6446 (p : Pattern) (selected : d96073 p = 1) : d98717 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d96037 q = 1) : d96037 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d96040 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6443 q selected
    | true =>
      simp only [d96040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6444 q selected
  have h3 (q : Pattern) (selected : d96041 q = 1) : d98706 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96041, d98706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96041, d98706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d96044 q = 1) : d96044 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d96045 q = 1) : d98707 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96045, d98707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96045, d98707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96071 q = 1) : d98715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96071, d98715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96071, d98715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d96072 q = 1) : d98716 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96072, d98716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96072, d98716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d96073 q = 1) : d98717 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96073, d98717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96073, d98717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6447 (p : Pattern) (selected : d2406 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2397 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro153 q selected
  have h2 (q : Pattern) (selected : d2219 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro153 q selected
    | true =>
      simp only [d2219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2398 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2220 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2399 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2400 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro154 q selected
  have h8 (q : Pattern) (selected : d2231 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro154 q selected
    | true =>
      simp only [d2231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d2403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d2403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d2232 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d2404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d2404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d2405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d2406 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro6448 (p : Pattern) (selected : d2408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2402 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro154 q selected
  have h2 (q : Pattern) (selected : d2231 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro154 q selected
    | true =>
      simp only [d2231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2403 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2232 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2404 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2405 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2408 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro6449 (p : Pattern) (selected : d2417 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2413 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro157 q selected
  have h2 (q : Pattern) (selected : d2246 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d2246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro157 q selected
    | true =>
      simp only [d2246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2414 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2247 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d2247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2415 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d2415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2416 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d2416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d2417 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d2417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro6450 (p : Pattern) (selected : d96118 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d96111 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6447 q selected
    | true =>
      simp only [d96111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6448 q selected
  have h2 (q : Pattern) (selected : d96112 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96113 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d96114 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6448 q selected
    | true =>
      simp only [d96114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6449 q selected
  have h5 (q : Pattern) (selected : d96115 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96116 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d96117 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d96118 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d96118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6451 (p : Pattern) (selected : d96122 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d96114 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d96114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6448 q selected
    | true =>
      simp only [d96114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6449 q selected
  have h2 (q : Pattern) (selected : d96115 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d96115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96116 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d96116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d96121 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d96121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96122 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d96122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6452 (p : Pattern) (selected : d96128 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d96119 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6450 q selected
    | true =>
      simp only [d96119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96120 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96123 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6451 q selected
    | true =>
      simp only [d96123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96124 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d96125 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96126 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d96127 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d96127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d96128 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d96128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro6453 (p : Pattern) (selected : d96132 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d96123 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d96123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6451 q selected
    | true =>
      simp only [d96123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96124 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d96124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96129 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d96129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96130 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d96130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96131 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d96131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96132 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d96132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6454 (p : Pattern) (selected : d96148 p = 1) : d98727 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d96110 q = 1) : d96110 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d96133 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d96133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6452 q selected
    | true =>
      simp only [d96133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6453 q selected
  have h3 (q : Pattern) (selected : d96134 q = 1) : d98723 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d96134, d98723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96134, d98723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d96144 q = 1) : d96144 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d96145 q = 1) : d98724 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d96145, d98724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96145, d98724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96146 q = 1) : d98725 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d96146, d98725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96146, d98725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d96147 q = 1) : d98726 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d96147, d98726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96147, d98726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d96148 q = 1) : d98727 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d96148, d98727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96148, d98727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro6455 (p : Pattern) (selected : d96165 p = 1) : d98733 p = 1 := by
  have h0 (q : Pattern) (selected : d95952 q = 1) : d95952 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d96049 q = 1) : d98711 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96049, d98711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6442 q selected
    | true =>
      simp only [d96049, d98711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6445 q selected
  have h2 (q : Pattern) (selected : d96067 q = 1) : d96067 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d96068 q = 1) : d98712 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96068, d98712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96068, d98712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d96069 q = 1) : d98713 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96069, d98713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96069, d98713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96070 q = 1) : d98714 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96070, d98714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96070, d98714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d96074 q = 1) : d98718 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96074, d98718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96074, d98718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6446 q selected
  have h8 (q : Pattern) (selected : d96076 q = 1) : d96076 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d96077 q = 1) : d98719 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96077, d98719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d96077, d98719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d96078 q = 1) : d98720 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96078, d98720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d96078, d98720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h11 (q : Pattern) (selected : d96079 q = 1) : d98721 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96079, d98721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d96079, d98721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h12 (q : Pattern) (selected : d96080 q = 1) : d98722 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96080, d98722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d96080, d98722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d96149 q = 1) : d98728 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d96149, d98728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96149, d98728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6454 q selected
  have h14 (q : Pattern) (selected : d96160 q = 1) : d96160 q = 1 := by
    exact selected
  have h15 (q : Pattern) (selected : d96161 q = 1) : d98729 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d96161, d98729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d96161, d98729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d96162 q = 1) : d98730 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d96162, d98730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d96162, d98730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h17 (q : Pattern) (selected : d96163 q = 1) : d98731 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d96163, d98731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d96163, d98731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h18 (q : Pattern) (selected : d96164 q = 1) : d98732 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d96164, d98732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d96164, d98732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h19 (q : Pattern) (selected : d96165 q = 1) : d98733 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d96165, d98733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d96165, d98733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro6456 (p : Pattern) (selected : d96171 p = 1) : d98739 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d96166 q = 1) : d98734 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96166, d98734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96166, d98734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6455 q selected
  have h2 (q : Pattern) (selected : d96167 q = 1) : d98735 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d96167, d98735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96167, d98735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d96168 q = 1) : d98736 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d96168, d98736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96168, d98736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d96169 q = 1) : d98737 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d96169, d98737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96169, d98737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d96170 q = 1) : d98738 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d96170, d98738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96170, d98738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d96171 q = 1) : d98739 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d96171, d98739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d96171, d98739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6457 (p : Pattern) (selected : d96177 p = 1) : d98745 p = 1 := by
  have h0 (q : Pattern) (selected : d95122 q = 1) : d98574 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d95122, d98574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6357 q selected
    | true =>
      simp only [d95122, d98574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6370 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d95383 q = 1) : d98614 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d95383, d98614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95383, d98614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6390 q selected
  have h3 (q : Pattern) (selected : d95384 q = 1) : d98615 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d95384, d98615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d95384, d98615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d95645 q = 1) : d98655 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d95645, d98655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95645, d98655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6412 q selected
  have h5 (q : Pattern) (selected : d95646 q = 1) : d98656 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d95646, d98656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95646, d98656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d95647 q = 1) : d98657 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d95647, d98657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d95647, d98657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d95908 q = 1) : d98697 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d95908, d98697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95908, d98697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6434 q selected
  have h8 (q : Pattern) (selected : d95909 q = 1) : d98698 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d95909, d98698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95909, d98698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d95910 q = 1) : d98699 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d95910, d98699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d95910, d98699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d95911 q = 1) : d98700 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d95911, d98700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d95911, d98700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d96172 q = 1) : d98740 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d96172, d98740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96172, d98740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6456 q selected
  have h12 (q : Pattern) (selected : d96173 q = 1) : d98741 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d96173, d98741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96173, d98741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d96174 q = 1) : d98742 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d96174, d98742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96174, d98742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d96175 q = 1) : d98743 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d96175, d98743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96175, d98743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d96176 q = 1) : d98744 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d96176, d98744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d96176, d98744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d96177 q = 1) : d98745 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d96177, d98745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d96177, d98745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro6458 (p : Pattern) (selected : d96183 p = 1) : d98751 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d96178 q = 1) : d98746 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d96178, d98746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6457 q selected
    | true =>
      simp only [d96178, d98746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96179 q = 1) : d98747 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d96179, d98747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96179, d98747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d96180 q = 1) : d98748 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d96180, d98748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96180, d98748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96181 q = 1) : d98749 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d96181, d98749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96181, d98749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96182 q = 1) : d98750 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d96182, d98750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96182, d98750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96183 q = 1) : d98751 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d96183, d98751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96183, d98751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6459 (p : Pattern) (selected : d96189 p = 1) : d98757 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d96184 q = 1) : d98752 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d96184, d98752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6458 q selected
    | true =>
      simp only [d96184, d98752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96185 q = 1) : d98753 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d96185, d98753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96185, d98753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d96186 q = 1) : d98754 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d96186, d98754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96186, d98754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96187 q = 1) : d98755 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d96187, d98755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96187, d98755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96188 q = 1) : d98756 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d96188, d98756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96188, d98756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96189 q = 1) : d98757 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d96189, d98757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96189, d98757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6460 (p : Pattern) (selected : d96195 p = 1) : d98763 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d96190 q = 1) : d98758 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d96190, d98758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6459 q selected
    | true =>
      simp only [d96190, d98758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96191 q = 1) : d98759 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d96191, d98759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96191, d98759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d96192 q = 1) : d98760 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d96192, d98760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96192, d98760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96193 q = 1) : d98761 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d96193, d98761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96193, d98761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96194 q = 1) : d98762 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d96194, d98762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96194, d98762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96195 q = 1) : d98763 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d96195, d98763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96195, d98763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6461 (p : Pattern) (selected : d96201 p = 1) : d98769 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d96196 q = 1) : d98764 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d96196, d98764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6460 q selected
    | true =>
      simp only [d96196, d98764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96197 q = 1) : d98765 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d96197, d98765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96197, d98765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d96198 q = 1) : d98766 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d96198, d98766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96198, d98766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96199 q = 1) : d98767 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d96199, d98767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96199, d98767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96200 q = 1) : d98768 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d96200, d98768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96200, d98768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96201 q = 1) : d98769 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d96201, d98769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96201, d98769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6462 (p : Pattern) (selected : d96207 p = 1) : d98775 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d96202 q = 1) : d98770 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d96202, d98770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6461 q selected
    | true =>
      simp only [d96202, d98770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96203 q = 1) : d98771 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d96203, d98771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96203, d98771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d96204 q = 1) : d98772 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d96204, d98772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96204, d98772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96205 q = 1) : d98773 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d96205, d98773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96205, d98773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96206 q = 1) : d98774 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d96206, d98774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96206, d98774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96207 q = 1) : d98775 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d96207, d98775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96207, d98775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6463 (p : Pattern) (selected : d96213 p = 1) : d98781 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d96208 q = 1) : d98776 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d96208, d98776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6462 q selected
    | true =>
      simp only [d96208, d98776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96209 q = 1) : d98777 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d96209, d98777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96209, d98777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d96210 q = 1) : d98778 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d96210, d98778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96210, d98778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96211 q = 1) : d98779 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d96211, d98779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96211, d98779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96212 q = 1) : d98780 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d96212, d98780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96212, d98780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96213 q = 1) : d98781 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d96213, d98781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96213, d98781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6464 (p : Pattern) (selected : d96219 p = 1) : d98787 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d96214 q = 1) : d98782 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d96214, d98782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6463 q selected
    | true =>
      simp only [d96214, d98782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d96215 q = 1) : d98783 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d96215, d98783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d96215, d98783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d96216 q = 1) : d98784 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d96216, d98784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d96216, d98784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d96217 q = 1) : d98785 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d96217, d98785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d96217, d98785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d96218 q = 1) : d98786 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d96218, d98786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d96218, d98786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d96219 q = 1) : d98787 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d96219, d98787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d96219, d98787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6465 (p : Pattern) (selected : d99418 p = 0) : d100022 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99413 q = 0) : d100017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99413, d100017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2894 q selected
    | true =>
      simp only [d99413, d100017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d99414 q = 0) : d100018 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99414, d100018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d99414, d100018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d99415 q = 0) : d100019 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99415, d100019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99415, d100019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99416 q = 0) : d100020 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99416, d100020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99416, d100020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99417 q = 0) : d100021 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99417, d100021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99417, d100021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d99418 q = 0) : d100022 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99418, d100022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99418, d100022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6466 (p : Pattern) (selected : d99424 p = 0) : d100028 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99413 q = 0) : d100017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99413, d100017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2894 q selected
    | true =>
      simp only [d99413, d100017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d99414 q = 0) : d100018 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99414, d100018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d99414, d100018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d99415 q = 0) : d100019 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99415, d100019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99415, d100019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99416 q = 0) : d100020 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99416, d100020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99416, d100020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99417 q = 0) : d100021 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99417, d100021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99417, d100021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d99419 q = 0) : d100023 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99419, d100023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2896 q selected
    | true =>
      simp only [d99419, d100023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d99420 q = 0) : d100024 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99420, d100024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d99420, d100024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d99421 q = 0) : d100025 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99421, d100025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d99421, d100025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d99422 q = 0) : d100026 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99422, d100026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99422, d100026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d99423 q = 0) : d100027 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99423, d100027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99423, d100027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d99424 q = 0) : d100028 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99424, d100028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d99424, d100028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro6467 (p : Pattern) (selected : d99429 p = 0) : d100033 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99419 q = 0) : d100023 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99419, d100023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2896 q selected
    | true =>
      simp only [d99419, d100023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d99420 q = 0) : d100024 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99420, d100024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d99420, d100024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d99421 q = 0) : d100025 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99421, d100025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99421, d100025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99422 q = 0) : d100026 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99422, d100026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99422, d100026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99423 q = 0) : d100027 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99423, d100027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99423, d100027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d99429 q = 0) : d100033 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99429, d100033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99429, d100033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6468 (p : Pattern) (selected : d99440 p = 0) : d100044 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99435 q = 0) : d100039 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99435, d100039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2899 q selected
    | true =>
      simp only [d99435, d100039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d99436 q = 0) : d100040 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99436, d100040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d99436, d100040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d99437 q = 0) : d100041 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99437, d100041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99437, d100041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99438 q = 0) : d100042 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99438, d100042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99438, d100042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99439 q = 0) : d100043 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99439, d100043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99439, d100043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d99440 q = 0) : d100044 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99440, d100044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99440, d100044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6469 (p : Pattern) (selected : d99446 p = 0) : d100050 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99425 q = 0) : d100029 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99425, d100029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6465 q selected
    | true =>
      simp only [d99425, d100029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6466 q selected
  have h2 (q : Pattern) (selected : d99426 q = 0) : d100030 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99426, d100030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d99426, d100030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d99427 q = 0) : d100031 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99427, d100031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99427, d100031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99428 q = 0) : d100032 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99428, d100032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99428, d100032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99430 q = 0) : d100034 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99430, d100034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99430, d100034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6467 q selected
  have h6 (q : Pattern) (selected : d99431 q = 0) : d100035 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99431, d100035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d99431, d100035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d99432 q = 0) : d100036 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99432, d100036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d99432, d100036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d99433 q = 0) : d100037 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99433, d100037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d99433, d100037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d99434 q = 0) : d100038 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99434, d100038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d99434, d100038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d99441 q = 0) : d100045 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99441, d100045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99441, d100045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6468 q selected
  have h11 (q : Pattern) (selected : d99442 q = 0) : d100046 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99442, d100046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d99442, d100046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d99443 q = 0) : d100047 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99443, d100047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d99443, d100047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d99444 q = 0) : d100048 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99444, d100048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d99444, d100048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d99445 q = 0) : d100049 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99445, d100049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d99445, d100049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d99446 q = 0) : d100050 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99446, d100050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d99446, d100050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro6470 (p : Pattern) (selected : d99456 p = 0) : d100060 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99413 q = 0) : d100017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99413, d100017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2894 q selected
    | true =>
      simp only [d99413, d100017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d99452 q = 0) : d100056 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99452, d100056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99452, d100056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99453 q = 0) : d100057 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99453, d100057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99453, d100057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99454 q = 0) : d100058 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99454, d100058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99454, d100058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99455 q = 0) : d100059 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99455, d100059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99455, d100059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d99456 q = 0) : d100060 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99456, d100060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99456, d100060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6471 (p : Pattern) (selected : d99463 p = 0) : d100067 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99413 q = 0) : d100017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99413, d100017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2894 q selected
    | true =>
      simp only [d99413, d100017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d99452 q = 0) : d100056 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99452, d100056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99452, d100056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99453 q = 0) : d100057 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99453, d100057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99453, d100057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99454 q = 0) : d100058 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99454, d100058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99454, d100058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99455 q = 0) : d100059 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99455, d100059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99455, d100059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d99419 q = 0) : d100023 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99419, d100023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2896 q selected
    | true =>
      simp only [d99419, d100023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d99459 q = 0) : d100063 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99459, d100063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99459, d100063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d99460 q = 0) : d100064 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99460, d100064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d99460, d100064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d99461 q = 0) : d100065 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99461, d100065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99461, d100065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d99462 q = 0) : d100066 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99462, d100066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99462, d100066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d99463 q = 0) : d100067 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99463, d100067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d99463, d100067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro6472 (p : Pattern) (selected : d99476 p = 0) : d100080 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d6740 q = 0) : d81528 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4219 q selected
    | true =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6741 q = 0) : d81529 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d81529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6741, d81529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99474 q = 0) : d100078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d99474, d100078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99474, d100078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99475 q = 0) : d100079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d99475, d100079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d99475, d100079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d99476 q = 0) : d100080 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d99476, d100080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99476, d100080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro6473 (p : Pattern) (selected : d99483 p = 0) : d100086 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99467 q = 0) : d100071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99467, d100071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2904 q selected
    | true =>
      simp only [d99467, d100071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d99468 q = 0) : d100072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99468, d100072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99468, d100072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99469 q = 0) : d100073 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99469, d100073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99469, d100073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99470 q = 0) : d100074 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99470, d100074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99470, d100074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99471 q = 0) : d100075 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99471, d100075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2905 q selected
    | true =>
      simp only [d99471, d100075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d99472 q = 0) : d100076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99472, d100076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99472, d100076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d99473 q = 0) : d100077 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99473, d100077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d99473, d100077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d99477 q = 0) : d100081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99477, d100081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6472 q selected
    | true =>
      simp only [d99477, d100081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2894 q selected
  have h9 (q : Pattern) (selected : d99478 q = 0) : d100017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99478, d100017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2907 q selected
    | true =>
      simp only [d99478, d100017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d99479 q = 0) : d100082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99479, d100082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d99479, d100082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d99480 q = 0) : d100083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99480, d100083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d99480, d100083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d99481 q = 0) : d100084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99481, d100084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d99481, d100084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d99482 q = 0) : d100085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99482, d100085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d99482, d100085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d99483 q = 0) : d100086 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99483, d100086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99483, d100086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro6474 (p : Pattern) (selected : d99491 p = 0) : d100094 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d6740 q = 0) : d81528 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4219 q selected
    | true =>
      simp only [d6740, d81528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6741 q = 0) : d81529 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6741, d81529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6741, d81529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99474 q = 0) : d100078 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d99474, d100078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99474, d100078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99475 q = 0) : d100079 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d99475, d100079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d99475, d100079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d99491 q = 0) : d100094 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d99491, d100094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d99491, d100094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6475 (p : Pattern) (selected : d99498 p = 0) : d100100 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99467 q = 0) : d100071 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99467, d100071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2904 q selected
    | true =>
      simp only [d99467, d100071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d99468 q = 0) : d100072 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99468, d100072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99468, d100072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99469 q = 0) : d100073 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99469, d100073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99469, d100073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99470 q = 0) : d100074 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99470, d100074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99470, d100074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99471 q = 0) : d100075 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99471, d100075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2905 q selected
    | true =>
      simp only [d99471, d100075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d99472 q = 0) : d100076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99472, d100076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99472, d100076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d99473 q = 0) : d100077 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99473, d100077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d99473, d100077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d99477 q = 0) : d100081 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99477, d100081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6472 q selected
    | true =>
      simp only [d99477, d100081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2894 q selected
  have h9 (q : Pattern) (selected : d99478 q = 0) : d100017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99478, d100017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2907 q selected
    | true =>
      simp only [d99478, d100017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d99479 q = 0) : d100082 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99479, d100082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d99479, d100082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d99480 q = 0) : d100083 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99480, d100083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d99480, d100083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d99481 q = 0) : d100084 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99481, d100084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d99481, d100084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d99482 q = 0) : d100085 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99482, d100085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d99482, d100085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d99484 q = 0) : d100087 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99484, d100087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2909 q selected
    | true =>
      simp only [d99484, d100087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d99485 q = 0) : d100088 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99485, d100088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99485, d100088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d99486 q = 0) : d100089 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99486, d100089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d99486, d100089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d99487 q = 0) : d100090 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99487, d100090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99487, d100090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d99488 q = 0) : d100091 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99488, d100091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2910 q selected
    | true =>
      simp only [d99488, d100091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d99489 q = 0) : d100092 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99489, d100092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99489, d100092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d99490 q = 0) : d100093 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99490, d100093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d99490, d100093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d99492 q = 0) : d100095 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99492, d100095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6474 q selected
    | true =>
      simp only [d99492, d100095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2896 q selected
  have h22 (q : Pattern) (selected : d99493 q = 0) : d100023 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99493, d100023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2912 q selected
    | true =>
      simp only [d99493, d100023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d99494 q = 0) : d100096 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99494, d100096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d99494, d100096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  have h24 (q : Pattern) (selected : d99495 q = 0) : d100097 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99495, d100097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d99495, d100097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d99496 q = 0) : d100098 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99496, d100098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d99496, d100098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d99497 q = 0) : d100099 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99497, d100099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d99497, d100099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d99498 q = 0) : d100100 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99498, d100100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d99498, d100100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro6476 (p : Pattern) (selected : d99500 p = 0) : d100102 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99413 q = 0) : d100017 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99413, d100017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2894 q selected
    | true =>
      simp only [d99413, d100017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d99452 q = 0) : d100056 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99452, d100056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99452, d100056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99453 q = 0) : d100057 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99453, d100057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99453, d100057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99454 q = 0) : d100058 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99454, d100058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99454, d100058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99455 q = 0) : d100059 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99455, d100059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99455, d100059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d99500 q = 0) : d100102 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99500, d100102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d99500, d100102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6477 (p : Pattern) (selected : d99507 p = 0) : d100109 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99492 q = 0) : d100095 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99492, d100095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6474 q selected
    | true =>
      simp only [d99492, d100095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2896 q selected
  have h2 (q : Pattern) (selected : d99493 q = 0) : d100023 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99493, d100023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2912 q selected
    | true =>
      simp only [d99493, d100023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d99494 q = 0) : d100096 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99494, d100096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d99494, d100096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d99495 q = 0) : d100097 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99495, d100097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d99495, d100097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d99505 q = 0) : d100107 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99505, d100107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99505, d100107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d99506 q = 0) : d100108 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99506, d100108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99506, d100108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d99507 q = 0) : d100109 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99507, d100109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99507, d100109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro6478 (p : Pattern) (selected : d99515 p = 0) : d100117 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d6773 q = 0) : d81561 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6773, d81561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4225 q selected
    | true =>
      simp only [d6773, d81561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6774 q = 0) : d81562 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6774, d81562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6774, d81562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99513 q = 0) : d100115 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d99513, d100115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99513, d100115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99514 q = 0) : d100116 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d99514, d100116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d99514, d100116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d99515 q = 0) : d100117 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d99515, d100117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d99515, d100117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6479 (p : Pattern) (selected : d99522 p = 0) : d100123 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99516 q = 0) : d100118 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99516, d100118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6478 q selected
    | true =>
      simp only [d99516, d100118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2899 q selected
  have h2 (q : Pattern) (selected : d99517 q = 0) : d100039 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99517, d100039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2916 q selected
    | true =>
      simp only [d99517, d100039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d99518 q = 0) : d100119 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99518, d100119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d99518, d100119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d99519 q = 0) : d100120 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99519, d100120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d99519, d100120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d99520 q = 0) : d100121 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99520, d100121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99520, d100121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d99521 q = 0) : d100122 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99521, d100122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99521, d100122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d99522 q = 0) : d100123 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99522, d100123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99522, d100123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro6480 (p : Pattern) (selected : d99528 p = 0) : d100129 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99457 q = 0) : d100061 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99457, d100061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99457, d100061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6470 q selected
  have h2 (q : Pattern) (selected : d99458 q = 0) : d100062 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99458, d100062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d99458, d100062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d99464 q = 0) : d100068 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99464, d100068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6470 q selected
    | true =>
      simp only [d99464, d100068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6471 q selected
  have h4 (q : Pattern) (selected : d99465 q = 0) : d100069 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99465, d100069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d99465, d100069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d99466 q = 0) : d100070 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99466, d100070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99466, d100070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d99499 q = 0) : d100101 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99499, d100101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6473 q selected
    | true =>
      simp only [d99499, d100101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6475 q selected
  have h7 (q : Pattern) (selected : d99501 q = 0) : d100103 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99501, d100103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6476 q selected
    | true =>
      simp only [d99501, d100103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d99502 q = 0) : d100104 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99502, d100104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d99502, d100104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d99503 q = 0) : d100105 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99503, d100105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d99503, d100105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d99504 q = 0) : d100106 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99504, d100106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d99504, d100106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d99508 q = 0) : d100110 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99508, d100110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99508, d100110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6477 q selected
  have h12 (q : Pattern) (selected : d99509 q = 0) : d100111 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99509, d100111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d99509, d100111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d99510 q = 0) : d100112 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99510, d100112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d99510, d100112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d99511 q = 0) : d100113 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99511, d100113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d99511, d100113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d99512 q = 0) : d100114 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99512, d100114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d99512, d100114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d99523 q = 0) : d100124 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99523, d100124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99523, d100124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6479 q selected
  have h17 (q : Pattern) (selected : d99524 q = 0) : d100125 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99524, d100125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d99524, d100125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d99525 q = 0) : d100126 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99525, d100126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d99525, d100126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d99526 q = 0) : d100127 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99526, d100127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d99526, d100127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d99527 q = 0) : d100128 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99527, d100128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d99527, d100128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d99528 q = 0) : d100129 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99528, d100129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d99528, d100129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro6481 (p : Pattern) (selected : d99534 p = 0) : d100135 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99447 q = 0) : d100051 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99447, d100051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99447, d100051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6469 q selected
  have h2 (q : Pattern) (selected : d99448 q = 0) : d100052 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99448, d100052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99448, d100052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99449 q = 0) : d100053 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99449, d100053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99449, d100053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d99450 q = 0) : d100054 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99450, d100054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99450, d100054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99451 q = 0) : d100055 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99451, d100055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99451, d100055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d99529 q = 0) : d100130 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99529, d100130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99529, d100130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6480 q selected
  have h7 (q : Pattern) (selected : d99530 q = 0) : d100131 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99530, d100131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99530, d100131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d99531 q = 0) : d100132 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99531, d100132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99531, d100132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d99532 q = 0) : d100133 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99532, d100133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99532, d100133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d99533 q = 0) : d100134 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99533, d100134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99533, d100134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d99534 q = 0) : d100135 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99534, d100135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d99534, d100135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro6482 (p : Pattern) (selected : d99540 p = 0) : d100141 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99535 q = 0) : d100136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99535, d100136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2920 q selected
    | true =>
      simp only [d99535, d100136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d99536 q = 0) : d100137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99536, d100137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99536, d100137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99537 q = 0) : d100138 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99537, d100138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99537, d100138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99538 q = 0) : d100139 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99538, d100139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99538, d100139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99539 q = 0) : d100140 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99539, d100140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99539, d100140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d99540 q = 0) : d100141 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99540, d100141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99540, d100141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6483 (p : Pattern) (selected : d99548 p = 0) : d100149 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99535 q = 0) : d100136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99535, d100136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2920 q selected
    | true =>
      simp only [d99535, d100136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d99536 q = 0) : d100137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99536, d100137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99536, d100137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99537 q = 0) : d100138 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99537, d100138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99537, d100138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99538 q = 0) : d100139 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99538, d100139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99538, d100139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99539 q = 0) : d100140 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99539, d100140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99539, d100140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d99543 q = 0) : d100144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99543, d100144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2922 q selected
    | true =>
      simp only [d99543, d100144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d99544 q = 0) : d100145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99544, d100145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99544, d100145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d99545 q = 0) : d100146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99545, d100146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d99545, d100146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d99546 q = 0) : d100147 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99546, d100147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99546, d100147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d99547 q = 0) : d100148 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99547, d100148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99547, d100148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d99548 q = 0) : d100149 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99548, d100149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d99548, d100149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro6484 (p : Pattern) (selected : d99561 p = 0) : d100162 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d6800 q = 0) : d81588 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d81588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4230 q selected
    | true =>
      simp only [d6800, d81588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6801 q = 0) : d81589 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d81589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6801, d81589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99559 q = 0) : d100160 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d99559, d100160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99559, d100160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99560 q = 0) : d100161 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d99560, d100161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d99560, d100161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d99561 q = 0) : d100162 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d99561, d100162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99561, d100162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro6485 (p : Pattern) (selected : d99568 p = 0) : d100168 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99552 q = 0) : d100153 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99552, d100153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2924 q selected
    | true =>
      simp only [d99552, d100153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d99553 q = 0) : d100154 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99553, d100154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99553, d100154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99554 q = 0) : d100155 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99554, d100155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99554, d100155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99555 q = 0) : d100156 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99555, d100156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99555, d100156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99556 q = 0) : d100157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99556, d100157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2925 q selected
    | true =>
      simp only [d99556, d100157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d99557 q = 0) : d100158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99557, d100158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99557, d100158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d99558 q = 0) : d100159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99558, d100159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d99558, d100159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d99562 q = 0) : d100163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99562, d100163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6484 q selected
    | true =>
      simp only [d99562, d100163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2920 q selected
  have h9 (q : Pattern) (selected : d99563 q = 0) : d100136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99563, d100136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2927 q selected
    | true =>
      simp only [d99563, d100136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d99564 q = 0) : d100164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99564, d100164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d99564, d100164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d99565 q = 0) : d100165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99565, d100165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d99565, d100165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d99566 q = 0) : d100166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99566, d100166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d99566, d100166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d99567 q = 0) : d100167 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99567, d100167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d99567, d100167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d99568 q = 0) : d100168 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99568, d100168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99568, d100168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro6486 (p : Pattern) (selected : d99576 p = 0) : d100176 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d6800 q = 0) : d81588 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6800, d81588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4230 q selected
    | true =>
      simp only [d6800, d81588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6801 q = 0) : d81589 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6801, d81589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6801, d81589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99559 q = 0) : d100160 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d99559, d100160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99559, d100160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99560 q = 0) : d100161 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d99560, d100161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d99560, d100161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d99576 q = 0) : d100176 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d99576, d100176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d99576, d100176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6487 (p : Pattern) (selected : d99583 p = 0) : d100182 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99552 q = 0) : d100153 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99552, d100153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2924 q selected
    | true =>
      simp only [d99552, d100153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d99553 q = 0) : d100154 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99553, d100154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99553, d100154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99554 q = 0) : d100155 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99554, d100155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99554, d100155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99555 q = 0) : d100156 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99555, d100156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99555, d100156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99556 q = 0) : d100157 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99556, d100157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2925 q selected
    | true =>
      simp only [d99556, d100157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d99557 q = 0) : d100158 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99557, d100158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99557, d100158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d99558 q = 0) : d100159 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99558, d100159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d99558, d100159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d99562 q = 0) : d100163 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99562, d100163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6484 q selected
    | true =>
      simp only [d99562, d100163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2920 q selected
  have h9 (q : Pattern) (selected : d99563 q = 0) : d100136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99563, d100136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2927 q selected
    | true =>
      simp only [d99563, d100136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d99564 q = 0) : d100164 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99564, d100164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d99564, d100164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d99565 q = 0) : d100165 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99565, d100165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d99565, d100165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d99566 q = 0) : d100166 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99566, d100166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d99566, d100166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d99567 q = 0) : d100167 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99567, d100167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d99567, d100167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d99569 q = 0) : d100169 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99569, d100169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2929 q selected
    | true =>
      simp only [d99569, d100169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d99570 q = 0) : d100170 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99570, d100170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99570, d100170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d99571 q = 0) : d100171 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99571, d100171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d99571, d100171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d99572 q = 0) : d100172 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99572, d100172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99572, d100172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d99573 q = 0) : d100173 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99573, d100173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2930 q selected
    | true =>
      simp only [d99573, d100173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d99574 q = 0) : d100174 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99574, d100174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99574, d100174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d99575 q = 0) : d100175 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99575, d100175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d99575, d100175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d99577 q = 0) : d100177 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99577, d100177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6486 q selected
    | true =>
      simp only [d99577, d100177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2922 q selected
  have h22 (q : Pattern) (selected : d99578 q = 0) : d100144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99578, d100144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2932 q selected
    | true =>
      simp only [d99578, d100144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d99579 q = 0) : d100178 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99579, d100178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d99579, d100178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  have h24 (q : Pattern) (selected : d99580 q = 0) : d100179 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99580, d100179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d99580, d100179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d99581 q = 0) : d100180 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99581, d100180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d99581, d100180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d99582 q = 0) : d100181 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99582, d100181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d99582, d100181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d99583 q = 0) : d100182 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99583, d100182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d99583, d100182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro6488 (p : Pattern) (selected : d99585 p = 0) : d100184 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99535 q = 0) : d100136 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99535, d100136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2920 q selected
    | true =>
      simp only [d99535, d100136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d99536 q = 0) : d100137 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99536, d100137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99536, d100137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99537 q = 0) : d100138 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99537, d100138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99537, d100138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99538 q = 0) : d100139 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99538, d100139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99538, d100139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99539 q = 0) : d100140 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99539, d100140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99539, d100140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d99585 q = 0) : d100184 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99585, d100184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d99585, d100184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro6489 (p : Pattern) (selected : d99592 p = 0) : d100191 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99577 q = 0) : d100177 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99577, d100177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6486 q selected
    | true =>
      simp only [d99577, d100177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2922 q selected
  have h2 (q : Pattern) (selected : d99578 q = 0) : d100144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99578, d100144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2932 q selected
    | true =>
      simp only [d99578, d100144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d99579 q = 0) : d100178 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99579, d100178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d99579, d100178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d99580 q = 0) : d100179 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99580, d100179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d99580, d100179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d99590 q = 0) : d100189 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99590, d100189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99590, d100189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d99591 q = 0) : d100190 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99591, d100190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99591, d100190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d99592 q = 0) : d100191 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99592, d100191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99592, d100191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro6490 (p : Pattern) (selected : d99600 p = 0) : d100199 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d6846 q = 0) : d81634 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6846, d81634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4239 q selected
    | true =>
      simp only [d6846, d81634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6847 q = 0) : d81635 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6847, d81635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6847, d81635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99598 q = 0) : d100197 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d99598, d100197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99598, d100197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99599 q = 0) : d100198 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d99599, d100198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d99599, d100198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d99600 q = 0) : d100199 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d99600, d100199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d99600, d100199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6491 (p : Pattern) (selected : d99607 p = 0) : d100206 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99601 q = 0) : d100200 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99601, d100200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6490 q selected
    | true =>
      simp only [d99601, d100200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2937 q selected
  have h2 (q : Pattern) (selected : d99602 q = 0) : d100201 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99602, d100201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2936 q selected
    | true =>
      simp only [d99602, d100201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d99603 q = 0) : d100202 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99603, d100202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d99603, d100202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d99604 q = 0) : d100203 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99604, d100203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d99604, d100203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d99605 q = 0) : d100204 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99605, d100204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99605, d100204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d99606 q = 0) : d100205 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99606, d100205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99606, d100205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d99607 q = 0) : d100206 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99607, d100206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99607, d100206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro6492 (p : Pattern) (selected : d99613 p = 0) : d100212 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99541 q = 0) : d100142 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99541, d100142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99541, d100142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6482 q selected
  have h2 (q : Pattern) (selected : d99542 q = 0) : d100143 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99542, d100143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d99542, d100143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d99549 q = 0) : d100150 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99549, d100150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6482 q selected
    | true =>
      simp only [d99549, d100150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6483 q selected
  have h4 (q : Pattern) (selected : d99550 q = 0) : d100151 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99550, d100151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d99550, d100151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d99551 q = 0) : d100152 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99551, d100152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99551, d100152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d99584 q = 0) : d100183 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99584, d100183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6485 q selected
    | true =>
      simp only [d99584, d100183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6487 q selected
  have h7 (q : Pattern) (selected : d99586 q = 0) : d100185 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99586, d100185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6488 q selected
    | true =>
      simp only [d99586, d100185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d99587 q = 0) : d100186 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99587, d100186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d99587, d100186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d99588 q = 0) : d100187 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99588, d100187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d99588, d100187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d99589 q = 0) : d100188 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99589, d100188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d99589, d100188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d99593 q = 0) : d100192 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99593, d100192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99593, d100192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6489 q selected
  have h12 (q : Pattern) (selected : d99594 q = 0) : d100193 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99594, d100193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d99594, d100193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d99595 q = 0) : d100194 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99595, d100194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d99595, d100194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d99596 q = 0) : d100195 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99596, d100195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d99596, d100195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d99597 q = 0) : d100196 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99597, d100196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d99597, d100196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d99608 q = 0) : d100207 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d99608, d100207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99608, d100207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6491 q selected
  have h17 (q : Pattern) (selected : d99609 q = 0) : d100208 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d99609, d100208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d99609, d100208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d99610 q = 0) : d100209 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d99610, d100209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d99610, d100209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d99611 q = 0) : d100210 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d99611, d100210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d99611, d100210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d99612 q = 0) : d100211 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d99612, d100211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d99612, d100211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d99613 q = 0) : d100212 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d99613, d100212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d99613, d100212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro6493 (p : Pattern) (selected : d99619 p = 0) : d100218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99614 q = 0) : d100213 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d99614, d100213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99614, d100213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6492 q selected
  have h2 (q : Pattern) (selected : d99615 q = 0) : d100214 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d99615, d100214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99615, d100214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99616 q = 0) : d100215 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d99616, d100215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99616, d100215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d99617 q = 0) : d100216 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99617, d100216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99617, d100216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99618 q = 0) : d100217 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d99618, d100217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99618, d100217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d99619 q = 0) : d100218 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d99619, d100218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99619, d100218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6494 (p : Pattern) (selected : d99626 p = 0) : d100225 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99621 q = 0) : d100220 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99621, d100220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2941 q selected
    | true =>
      simp only [d99621, d100220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d99622 q = 0) : d100221 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99622, d100221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99622, d100221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99623 q = 0) : d100222 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99623, d100222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99623, d100222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99624 q = 0) : d100223 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99624, d100223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99624, d100223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99625 q = 0) : d100224 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99625, d100224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99625, d100224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d99626 q = 0) : d100225 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99626, d100225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99626, d100225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro6495 (p : Pattern) (selected : d99634 p = 0) : d100233 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99621 q = 0) : d100220 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99621, d100220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2941 q selected
    | true =>
      simp only [d99621, d100220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d99622 q = 0) : d100221 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99622, d100221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99622, d100221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99623 q = 0) : d100222 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99623, d100222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99623, d100222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99624 q = 0) : d100223 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99624, d100223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99624, d100223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99625 q = 0) : d100224 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99625, d100224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99625, d100224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d99629 q = 0) : d100228 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99629, d100228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2943 q selected
    | true =>
      simp only [d99629, d100228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d99630 q = 0) : d100229 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99630, d100229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99630, d100229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d99631 q = 0) : d100230 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99631, d100230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d99631, d100230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d99632 q = 0) : d100231 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99632, d100231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99632, d100231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d99633 q = 0) : d100232 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99633, d100232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99633, d100232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d99634 q = 0) : d100233 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99634, d100233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d99634, d100233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro6496 (p : Pattern) (selected : d99647 p = 0) : d100246 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d6878 q = 0) : d81666 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d81666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4245 q selected
    | true =>
      simp only [d6878, d81666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6879 q = 0) : d81667 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d81667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6879, d81667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99645 q = 0) : d100244 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d99645, d100244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99645, d100244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99646 q = 0) : d100245 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d99646, d100245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d99646, d100245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d99647 q = 0) : d100246 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d99647, d100246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99647, d100246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro6497 (p : Pattern) (selected : d99654 p = 0) : d100252 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99638 q = 0) : d100237 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99638, d100237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2945 q selected
    | true =>
      simp only [d99638, d100237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d99639 q = 0) : d100238 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99639, d100238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99639, d100238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99640 q = 0) : d100239 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99640, d100239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99640, d100239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99641 q = 0) : d100240 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99641, d100240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99641, d100240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99642 q = 0) : d100241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99642, d100241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2946 q selected
    | true =>
      simp only [d99642, d100241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d99643 q = 0) : d100242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99643, d100242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99643, d100242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d99644 q = 0) : d100243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99644, d100243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d99644, d100243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d99648 q = 0) : d100247 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99648, d100247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6496 q selected
    | true =>
      simp only [d99648, d100247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2941 q selected
  have h9 (q : Pattern) (selected : d99649 q = 0) : d100220 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99649, d100220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2948 q selected
    | true =>
      simp only [d99649, d100220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d99650 q = 0) : d100248 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99650, d100248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d99650, d100248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d99651 q = 0) : d100249 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99651, d100249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d99651, d100249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d99652 q = 0) : d100250 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99652, d100250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d99652, d100250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d99653 q = 0) : d100251 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99653, d100251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d99653, d100251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d99654 q = 0) : d100252 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99654, d100252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99654, d100252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro6498 (p : Pattern) (selected : d99662 p = 0) : d100260 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d6878 q = 0) : d81666 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d6878, d81666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4245 q selected
    | true =>
      simp only [d6878, d81666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d6879 q = 0) : d81667 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d6879, d81667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d6879, d81667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99645 q = 0) : d100244 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d99645, d100244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99645, d100244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99646 q = 0) : d100245 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d99646, d100245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d99646, d100245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d99662 q = 0) : d100260 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d99662, d100260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d99662, d100260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro6499 (p : Pattern) (selected : d99669 p = 0) : d100266 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d99638 q = 0) : d100237 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99638, d100237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2945 q selected
    | true =>
      simp only [d99638, d100237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d99639 q = 0) : d100238 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99639, d100238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99639, d100238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d99640 q = 0) : d100239 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99640, d100239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d99640, d100239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d99641 q = 0) : d100240 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99641, d100240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99641, d100240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d99642 q = 0) : d100241 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99642, d100241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2946 q selected
    | true =>
      simp only [d99642, d100241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d99643 q = 0) : d100242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99643, d100242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99643, d100242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d99644 q = 0) : d100243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99644, d100243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d99644, d100243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d99648 q = 0) : d100247 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99648, d100247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6496 q selected
    | true =>
      simp only [d99648, d100247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2941 q selected
  have h9 (q : Pattern) (selected : d99649 q = 0) : d100220 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99649, d100220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2948 q selected
    | true =>
      simp only [d99649, d100220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d99650 q = 0) : d100248 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99650, d100248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d99650, d100248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d99651 q = 0) : d100249 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99651, d100249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d99651, d100249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d99652 q = 0) : d100250 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99652, d100250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d99652, d100250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d99653 q = 0) : d100251 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99653, d100251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d99653, d100251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d99655 q = 0) : d100253 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99655, d100253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2950 q selected
    | true =>
      simp only [d99655, d100253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d99656 q = 0) : d100254 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99656, d100254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99656, d100254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d99657 q = 0) : d100255 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99657, d100255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d99657, d100255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d99658 q = 0) : d100256 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99658, d100256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99658, d100256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d99659 q = 0) : d100257 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99659, d100257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2951 q selected
    | true =>
      simp only [d99659, d100257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d99660 q = 0) : d100258 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99660, d100258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d99660, d100258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d99661 q = 0) : d100259 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99661, d100259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d99661, d100259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d99663 q = 0) : d100261 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99663, d100261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6498 q selected
    | true =>
      simp only [d99663, d100261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2943 q selected
  have h22 (q : Pattern) (selected : d99664 q = 0) : d100228 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d99664, d100228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro2953 q selected
    | true =>
      simp only [d99664, d100228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d99665 q = 0) : d100262 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d99665, d100262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d99665, d100262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  have h24 (q : Pattern) (selected : d99666 q = 0) : d100263 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d99666, d100263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d99666, d100263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d99667 q = 0) : d100264 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d99667, d100264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d99667, d100264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d99668 q = 0) : d100265 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d99668, d100265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d99668, d100265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d99669 q = 0) : d100266 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d99669, d100266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d99669, d100266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
end NetHack.Soko22Hazard87
